theory HashTrie
  imports Main
begin
(*-------------------------------------------HashTrie-------------------------------------------*)
type_synonym 'a array = "'a list"

definition arr_query :: "'a array \<Rightarrow> nat \<Rightarrow> 'a" ("_[_]")
  where "a[i] = a ! i"

type_synonym string = "char list"
datatype 'v hashtrie = Trie "'v option" "'v hashtrie list"
primrec h_malloc_line:: "nat \<Rightarrow> ('v hashtrie) list"
  where "h_malloc_line 0 = []"|
        "h_malloc_line (Suc n)  =  (Trie None []) # (h_malloc_line n)"
primrec h_malloc::"nat \<Rightarrow> nat \<Rightarrow> ('v hashtrie) list list"
  where"h_malloc 0 m = []"|
       "h_malloc (Suc n) m = (h_malloc_line m) # (h_malloc n m)"
definition "hashtrie_node = (h_malloc_line 256)"
definition "head_index = (h_malloc 256 256)"
lemma mal_nonempty:"n > 0 \<Longrightarrow> h_malloc_line n \<noteq> []"
  apply(induct n)
  apply simp+
  done
(* value "hashtrie_node"*)
(*value"head_index"*)

primrec "value"::"'v hashtrie \<Rightarrow> 'v option"
  where "value (Trie ov al) = ov"
primrec "alist"::"'v hashtrie \<Rightarrow> 'v hashtrie list"
  where "alist (Trie ov al) = al"

fun isless_hashlength::"nat list \<Rightarrow> string hashtrie \<Rightarrow> bool"
  where "isless_hashlength [] (Trie _ _) = True" |
        "isless_hashlength (x#xs) (Trie _ l) = (if x < length l \<and> l \<noteq> [] then isless_hashlength xs (l!x) else False)"
primrec ht_updata::"nat list \<Rightarrow> 'v hashtrie \<Rightarrow> 'v \<Rightarrow> 'v hashtrie"
  where"ht_updata [] t v= Trie (Some v) (alist t)"|
       "ht_updata (x # xs) t v=(let tt = (case (alist t)[x] of (Trie va []) \<Rightarrow> 
                                            (if xs \<noteq> [] then Trie va hashtrie_node else Trie va []) |
                                               at \<Rightarrow> at) 
                                in Trie (value t) (alist t[x:=(ht_updata xs tt v)]))"

fun isin_ht::"'v hashtrie \<Rightarrow> nat list \<Rightarrow> bool"
  where "isin_ht (Trie v _) [] = (if v=None then False else True)" |
        "isin_ht (Trie v l) (x#xs) = (if l = [] then False 
                                     else (if (l!x) = Trie None [] then False 
                                                            else isin_ht (l!x) xs))"

definition set_ht::"'v hashtrie \<Rightarrow> (nat list) set"
  where "set_ht ht = {m. isin_ht ht m}"

(*----------------------------------------Proof_HashTrie----------------------------------------*)
lemma upht_nonepmty:"\<And>ht v . m \<noteq> [] \<Longrightarrow> alist ht \<noteq> [] \<Longrightarrow> alist (ht_updata m ht v) \<noteq> []"
  apply(induct m)
  apply simp
  apply simp
  done

lemma one_isinupht:"\<And>a ht v. a < length (alist ht) \<Longrightarrow>(isin_ht (Trie (value ht) (alist ht[a := Trie (Some v) []]))) [a]"
  by auto
lemma more_one_isless:"isless_hashlength (a # m) ht = (a < length (alist ht) \<and> isless_hashlength m ((alist(ht))!a))"
  apply auto
  using isless_hashlength.elims(2) apply fastforce
  apply (metis alist.simps hashtrie.exhaust isless_hashlength.simps(2))
  by (metis alist.simps hashtrie.exhaust isless_hashlength.simps(2) list.size(3) not_less_zero)
lemma one_isless:"isless_hashlength [a] ht \<Longrightarrow> a < length (alist ht)"
  apply (induct ht)
  apply simp
  apply (split if_splits)
  apply auto
  done
lemma upht_to_ht:"x = aa#as \<Longrightarrow> 
          x \<noteq> [a] \<Longrightarrow>
          isless_hashlength [a] ht \<Longrightarrow>
          isin_ht (Trie (value ht) (alist ht[a := Trie (Some v) []])) x \<Longrightarrow>  isin_ht ht x"
  apply simp
  apply (split if_splits)
  apply simp
  apply (split if_splits)
  apply auto
  using isin_ht.elims(3) apply fastforce
  apply (case_tac \<open>aa=a\<close>)
  apply simp
  using isin_ht.elims(2) one_isless apply fastforce
  using isin_ht.elims(3) by fastforce
lemma newstr_more_two:"isless_hashlength (a # m) ht \<Longrightarrow> alist ht[a] = Trie va h \<Longrightarrow> m \<noteq> [] \<Longrightarrow> h = [] \<Longrightarrow>
        set_ht (Trie (value ht) (alist ht[a := ht_updata m (Trie va hashtrie_node) v])) = insert (a # m) (set_ht ht)"
  by (metis (no_types, lifting) alist.simps gr_implies_not0 isless_hashlength.elims(2) 
       list.distinct(1) list.sel(3) list.size(3) nth_Cons_0 arr_query_def)
lemma newstr_only_one:" isless_hashlength (a # m) ht \<Longrightarrow> alist ht[a] = Trie va h \<Longrightarrow>  \<not> m \<noteq> [] \<Longrightarrow> h = [] \<Longrightarrow>
        set_ht (Trie (value ht) (alist ht[a := ht_updata m (Trie va []) v])) = insert (a # m) (set_ht ht)"
  apply(simp add:set_ht_def arr_query_def)
  by(smt Collect_cong alist.simps one_isinupht insert_Collect isin_ht.elims(2) isin_ht.simps(1) 
          isin_ht.simps(2) isless_hashlength.elims(2) one_isless nth_list_update_neq upht_to_ht value.simps)
lemma newstr_more_one: "(\<And>ht v. isless_hashlength m ht \<Longrightarrow> set_ht (ht_updata m ht v) = insert m (set_ht ht)) \<Longrightarrow>
        isless_hashlength (a # m) ht \<Longrightarrow> h = h1 # h2 \<Longrightarrow> alist ht[a] = Trie va (h1 # h2) \<Longrightarrow> 
        set_ht (Trie (value ht) (alist ht[a := ht_updata m (Trie va (h1 # h2)) v])) = insert (a # m) (set_ht ht)"
  apply (auto simp:set_ht_def arr_query_def)
  apply (smt alist.simps insert_iff isin_ht.elims(2) isin_ht.elims(3) isless_hashlength.elims(2) list.distinct(1) 
            list.sel(3) mem_Collect_eq nth_Cons_0 nth_list_update_eq nth_list_update_neq value.simps)
  apply (smt alist.simps insertI1 isin_ht.simps(1) isless_hashlength.elims(2) list.distinct(1)
            list.sel(3) mem_Collect_eq nth_Cons_0 nth_list_update_eq upht_nonepmty)
  using isless_hashlength.elims(2) apply fastforce
  apply (smt alist.simps insertCI isless_hashlength.elims(2) list.distinct(1) 
            list.sel(3) mem_Collect_eq nth_Cons_0 nth_list_update_eq)
  by (smt alist.simps insertCI isin_ht.elims(2) isin_ht.elims(3) isless_hashlength.elims(2) list.discI 
            list.inject list_update_nonempty mem_Collect_eq nth_list_update_eq nth_list_update_neq value.simps)
theorem upht_correct:"\<And>hashtrie v. isless_hashlength new_str hashtrie \<Longrightarrow> 
                    set_ht (ht_updata new_str hashtrie v) = {new_str} \<union> set_ht hashtrie"
  apply (induct new_str)
  apply (simp add:set_ht_def,smt Collect_cong alist.simps insert_Collect isin_ht.elims(2)
          isin_ht.elims(3) isin_ht.simps(1) list.inject option.discI)
  apply(simp ,split hashtrie.splits,rule allI,rule allI,split list.splits)
  using newstr_more_two newstr_only_one newstr_more_one by auto

thm isless_hashlength.elims
definition "kw2 = [0::nat,0,1,1]"

fun uphead::"nat list \<Rightarrow> (string hashtrie) list list \<Rightarrow> string \<Rightarrow> (string hashtrie) list list"
  where "uphead (f#s#l) h v = (let tt = (case h[f][s] of (Trie va []) => Trie va hashtrie_node |
                                            at \<Rightarrow> at) in h[f:=(h[f])[s:=ht_updata l tt v]])"
primrec head_hash_table::"nat list list \<Rightarrow> string list \<Rightarrow> (string hashtrie) list list \<Rightarrow> (string hashtrie) list list"
  where "head_hash_table [] vs h = h"|
        "head_hash_table (x#xs) vs h = (let l = (if ((x[0])>128) then x
                                       else (x[0])#x) in head_hash_table xs (tl vs) (uphead l h (hd vs)))"

primrec find_p::"nat list \<Rightarrow> string hashtrie \<Rightarrow> string hashtrie option"
  where "find_p [] t = Some t"|
        "find_p (x#xs) t = (if alist t = [] then None 
                                  else (case (alist t)[x] of Trie None [] \<Rightarrow> None |
                                                     Trie _ _ \<Rightarrow> find_p xs ((alist t)!x)))"

(*----------------------------------------Violent Matching----------------------------------------*)
fun c_vmatching::"nat list \<Rightarrow> string hashtrie \<Rightarrow> string list \<Rightarrow> string list"
  where "c_vmatching [] ht p = (case (value ht) of Some v \<Rightarrow> (v#p) |
                                        None \<Rightarrow> p)" |
         "c_vmatching (x#[]) ht p = (case (value ht) of Some v \<Rightarrow> (v#p) |
                                             None \<Rightarrow> p)"|
         "c_vmatching (x#n#xs) ht p = (case (value ht) of Some v \<Rightarrow> (v#p)|
                                          None \<Rightarrow> (case (find_p [x,n] ht) of None \<Rightarrow> p|
                                                                      (Some ht') \<Rightarrow> c_vmatching xs ht' p))"
primrec e_vmatching::"nat list \<Rightarrow> string hashtrie \<Rightarrow> string list \<Rightarrow> string list"
  where"e_vmatching [] ht p = (case (value ht) of Some v \<Rightarrow> (p@[v]) |
                                        None \<Rightarrow>  p)"|
        "e_vmatching (x#xs) ht p = (case (value ht) of Some v \<Rightarrow> (p@[v]) |
                                           None \<Rightarrow> (case find_p [x] ht of None \<Rightarrow> p|
                                                                    Some ht' \<Rightarrow> e_vmatching xs ht' p))"
fun vmatching::"nat list \<Rightarrow> string hashtrie list list \<Rightarrow> string list \<Rightarrow> string list"
  where"vmatching [] h p = p"|
       "vmatching (x#xs) h p = (if x>128 \<and> length xs \<ge> 3
                          then (case xs of (xx#a#aa#as) \<Rightarrow>
                                     (case find_p [a,aa] (h[x][xx]) of None \<Rightarrow> vmatching (a#aa#as) h p |
                                                              Some ht \<Rightarrow>                                                                                                                            
                                        (let n_p = c_vmatching as ht p in vmatching (a#aa#as) h n_p)))
                           else (if x>128 \<and> length xs < 3 then p
                               else (case xs of [] \<Rightarrow> p| (xx#as) \<Rightarrow> 
(case find_p [xx] (h[x][x]) of None \<Rightarrow> vmatching xs h p |
                                                                   Some ht \<Rightarrow>
                                                      (let n_p = e_vmatching as ht p in vmatching xs h n_p)))))"

(*----------------------------------------Threaded HashTrie----------------------------------------*)
definition find_prefix::"nat list \<Rightarrow> (string hashtrie) list list \<Rightarrow> string hashtrie option"
  where "find_prefix k h = (case k of (x#xs) \<Rightarrow> (if (x > 128) then find_p (tl xs) (h[x][(hd xs)])
                                                  else find_p xs (h!x!x)))"
lemma [simp]:"as \<noteq> [] \<Longrightarrow> find_p as (Trie v []) = None"
  apply (case_tac as)
  apply (simp)
  apply (simp)
  done
lemma [simp]:"\<And>bs v. as \<noteq> [] \<Longrightarrow> bs \<noteq>[] \<Longrightarrow> find_p as (Trie v bs) = (case bs[(hd as)] of Trie None [] \<Rightarrow> None |Trie v l \<Rightarrow> find_p (tl as) (bs[(hd as)])) "
  apply(induct as)
  apply (simp add:arr_query_def)                     
  apply (auto)
  by (metis arr_query_def alist.simps list.sel(1) list.sel(3))
(*findex*)
primrec ispre::" nat list list \<Rightarrow> nat list \<Rightarrow> nat list option"
  where"ispre [] s = None" |
       "ispre (x#xs) s = (if (take (length s) x) = s then Some s else ispre xs s)"
lemma ispre_r1:"ispre ks s = Some bs \<Longrightarrow> \<exists>xs. xs \<in> set ks \<and> set bs \<subseteq> set xs"
  apply (induct ks)
  apply simp
  apply simp
  apply (simp split:if_split_asm)
  apply (metis set_take_subset)
  by auto
lemma ispre_r2:"\<And>as. ispre ks as = Some bs  \<Longrightarrow> set bs = set as" 
  apply (induct ks)
  apply simp
  by (smt ispre.simps(1) ispre.simps(2) option.distinct(1) option.sel)
(*English*)
primrec e_common_pre_suf ::"nat list \<Rightarrow> nat list list \<Rightarrow> nat list option"
  where"e_common_pre_suf [] ks = None" |
       "e_common_pre_suf (x#xs) ks = (case ispre ks (x#xs) of Some s \<Rightarrow> Some s |
                                                          None \<Rightarrow> e_common_pre_suf xs ks)"
lemma e_common_pre_suf_set1[simp]:"e_common_pre_suf as ks = Some bs \<Longrightarrow> set bs \<subseteq> set as"
  apply (induct as)
  apply simp
  apply simp
  apply (simp split: option.split_asm )
  apply auto[1]
  apply (simp add:ispre_r2)
  done
lemma e_common_pre_suf_set2[simp]:"e_common_pre_suf as ks = Some bs \<Longrightarrow> \<exists>xs. xs \<in>set ks \<and> set bs \<subseteq> set xs"
  apply (induct as)
  apply simp
  apply simp
  apply (simp split: option.split_asm add:ispre_r1)
  done
primrec e_findex_l::"nat list \<Rightarrow> nat list \<Rightarrow> nat list list \<Rightarrow> (nat list \<times> string hashtrie) list  
          => (string hashtrie) list list \<Rightarrow> (nat list \<times> string hashtrie) list "
  where "e_findex_l [] p ks f h = f"|
        "e_findex_l (x#xs) p ks f h =(let i = (case e_common_pre_suf p ks of None \<Rightarrow> ([], Trie None [])|
                                                                   Some s \<Rightarrow> (s,the (find_prefix s h))) 
                                      in e_findex_l xs (p@[x]) ks (f@[i]) h)"
lemma e_findex_l_appendiseq:"\<And>l ks fa fb h. e_findex_l as l ks (fa@fb) h = fa @ (e_findex_l as l ks fb h)"
  apply (induct as)
  apply simp
  apply simp
  done
lemma e_findex_l_consiseq:"\<And>l ks x h. e_findex_l as l ks (x#[]) h = x # (e_findex_l as l ks [] h)"
  apply (induct as)
  apply simp
  apply simp
  by (metis (no_types, lifting) append_Cons append_Nil e_findex_l_appendiseq)
lemma e_findex_l_appen_nil_leniseq:"\<And>pa pb ls f h. length (e_findex_l as (pa @ pb) ks f h) =  length (e_findex_l as (pa @ []) ks f h)"
  apply (induct as)
  apply simp
  apply simp
  apply (auto simp:e_findex_l_appendiseq e_findex_l_consiseq)
  done
lemma e_findex_l_nil_leniseq:"\<And>pre. length (e_findex_l as pre ks [] h) = length as"
  apply (induct as)
  apply simp
  apply simp
  apply (simp split: option.split)
  by (simp add: e_findex_l_consiseq)
lemma e_findex_l_leniseq:"\<And>pre. length (e_findex_l as pre ks (f@[]) h) = length as + length f"
  apply (induct as)
  apply simp
  by (metis add.commute e_findex_l_appendiseq e_findex_l_nil_leniseq length_append)
definition e_findex_line::"nat list \<Rightarrow> nat list list  \<Rightarrow> (string hashtrie) list list \<Rightarrow> (nat list \<times> string hashtrie) list"
  where "e_findex_line k ks h = (case k of x#xs \<Rightarrow>e_findex_l (tl xs) [hd xs] ks [([], Trie None []),([], Trie None [])] h)"
(*English*)
(*Chinese*)
fun c_common_pre_suf ::"nat list \<Rightarrow> nat list list \<Rightarrow> nat list option"
  where"c_common_pre_suf [] ks = None" |
       "c_common_pre_suf (x#[]) ks = None"|
       "c_common_pre_suf (x#s#xs) ks = (case ispre ks (x#s#xs) of Some s \<Rightarrow> Some s |
                                                          None \<Rightarrow> c_common_pre_suf xs ks)"
value "c_common_pre_suf [3,3,2,3,2,3] [[0::nat,1,0,1],[2,3,2,3,3,2],[2,3,2,2,2,3]]"
lemma c_common_pre_suf_set1[simp]:"\<And>n bs. c_common_pre_suf as ks = Some bs \<Longrightarrow> set bs \<subseteq> set as"
  apply (induct as ks rule:c_common_pre_suf.induct)
  apply simp
  apply simp
  apply (simp split: option.splits)
  apply auto[1]
  apply (simp add:ispre_r2)
  done
lemma c_common_pre_suf_set2[simp]:"c_common_pre_suf as ks = Some bs \<Longrightarrow> \<exists>xs. xs \<in>set ks \<and> set bs \<subseteq> set xs"
  apply (induct as ks rule:c_common_pre_suf.induct)
  apply simp
  apply simp
  apply (simp split: option.split_asm add:ispre_r1)
  done
fun c_findex_l::"nat list \<Rightarrow> nat list \<Rightarrow> nat list list \<Rightarrow> (nat list \<times> string hashtrie) list  
          => (string hashtrie) list list \<Rightarrow> (nat list \<times> string hashtrie) list "
  where "c_findex_l [] p ks f h = f"|
        "c_findex_l (x#a#xs) p ks f h =(let i = (case c_common_pre_suf p ks of None \<Rightarrow> ([], Trie None [])|
                                                                   Some s \<Rightarrow> (s, the (find_prefix s h))) 
                                      in (c_findex_l  xs (p@[x,a]) ks (f@[i,i]) h))"
lemma c_findex_l_appendiseq:"\<And>n. (length as) = n*2 \<Longrightarrow> c_findex_l as l ks (fa@fb) h = fa @ (c_findex_l as l ks fb h)"
  apply(induct as l ks fb h rule:c_findex_l.induct)
  by (simp,subgoal_tac \<open>length xs = (n-1)*2\<close>,auto simp:Let_def)
lemma c_findex_l_leniseq:"\<And>n. (length as) = n*2 \<Longrightarrow> 
      length (c_findex_l as pre ks (f@[]) h) = length as + length f"
  apply(induct as pre ks f h rule:c_findex_l.induct)
  by(simp, subgoal_tac \<open>length xs = (n-1)*2\<close>,auto simp:option.split simp:Let_def)

definition c_findex_line::"nat list \<Rightarrow> nat list list  \<Rightarrow> (string hashtrie) list list \<Rightarrow> (nat list \<times> string hashtrie) list"
  where "c_findex_line k ks h = (case k of x#s#xs \<Rightarrow>
                                  c_findex_l (drop 2 xs) (take 2 xs) ks [([], Trie None []),([], Trie None []),([], Trie None []),([], Trie None [])] h)"
(*Chinese*)
primrec findex::"nat list list \<Rightarrow> nat list list \<Rightarrow> (nat list \<times> string hashtrie) list list  \<Rightarrow> (string hashtrie) list list \<Rightarrow> (nat list \<times> string hashtrie) list list"
  where "findex [] ks f h = f"|
        "findex (x#xs) ks f h =(let l = (if (hd x) > 128 then (f@[(c_findex_line x (ks@xs) h)])
                                               else  (f@[(e_findex_line x (ks@xs) h)])) in findex xs (ks@[x]) l h)"
lemma findex_append_nil:"\<And>ks f h. findex l ks f h = f@(findex l ks [] h)"
  apply (induct l)
  apply simp
proof -
fix a :: "nat list" and la :: "nat list list" and ks :: "nat list list" and f :: "(nat list \<times> char list hashtrie) list list" and h :: "char list hashtrie list list"
  assume a1: "\<And>ks f h. findex la ks f h = f @ findex la ks [] h"
  have f2: "\<forall>ns nss nssa pss hss. if 128 < hd ns then findex (ns # nss) nssa pss hss = findex nss (nssa @ [ns]) (pss @ [c_findex_line ns (nssa @ nss) hss]) hss else findex (ns # nss) nssa pss hss = findex nss (nssa @ [ns]) (pss @ [e_findex_line ns (nssa @ nss) hss]) hss"
    using findex.simps(2) by presburger
  then have f3: "\<not> 128 < hd a \<longrightarrow> findex (a # la) ks f h = (f @ [e_findex_line a (ks @ la) h]) @ findex la (ks @ [a]) [] h"
    using a1 by metis
  { assume "findex (a # la) ks f h \<noteq> f @ findex (a # la) ks [] h"
    moreover
    {assume "findex (a # la) ks f h \<noteq> f @ [c_findex_line a (ks @ la) h] @ findex la (ks @ [a]) [] h"
  then have "findex (a # la) ks f h \<noteq> findex la (ks @ [a]) (f @ [c_findex_line a (ks @ la) h]) h"
  using a1 by (metis (no_types) append.assoc)
  then have "\<not> 128 < hd a"
  using f2 by meson }
  ultimately have "findex (a # la) ks f h = f @ findex (a # la) ks [] h"
  using f3 f2 a1 by (metis append.assoc append_Nil) }
then show "findex (a # la) ks f h = f @ findex (a # la) ks [] h"
  by meson
qed

lemma findex_c_c:"i < Suc (length l) \<Longrightarrow> 128 < hd ((a # l)[i]) \<Longrightarrow> 128 < hd a \<Longrightarrow> 
       (\<And>i h p. i < length l \<Longrightarrow> 128 < hd (l[i]) \<Longrightarrow> findex l p [] h[i] = c_findex_line (l[i]) (p @ take i l @ drop (Suc i) l) h) \<Longrightarrow>
       findex l (p @ [a]) [c_findex_line a (p @ l) h] h[i] = c_findex_line ((a # l)[i]) (p @ take i (a # l) @ drop i l) h" 
  apply (case_tac "i = 0")
  apply (metis append_Cons drop_0 findex_append_nil nth_Cons_0 self_append_conv2 take_0 arr_query_def)
  by (metis (no_types, lifting) append.assoc append_Cons append_Nil findex_append_nil less_Suc_eq_0_disj nth_Cons_Suc take_Suc_Cons arr_query_def)
lemma findex_c_e:"\<lbrakk>i < Suc (length l); 128 < hd ((a # l)[i]); \<not> 128 < hd a;
       (\<And>i h p. \<lbrakk>i < length l; 128 < hd (l[i])\<rbrakk> \<Longrightarrow> findex l p [] h[i] = c_findex_line (l[i]) (p @ take i l @ drop (Suc i) l) h)\<rbrakk> \<Longrightarrow>
        findex l (p @ [a]) [e_findex_line a (p @ l) h] h[i] = c_findex_line ((a # l)[i]) (p @ take i (a # l) @ drop i l) h"
  by (smt append.assoc append_Cons findex_append_nil less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc self_append_conv2 take_Suc_Cons arr_query_def)
theorem findex_c:"\<And>i h p. \<lbrakk>i < length l ; hd (l[i]) > 128\<rbrakk> \<Longrightarrow> 
               (findex l p [] h)[i] = c_findex_line (l[i]) (p@(take i l)@(drop (i+1) l)) h"
  apply(induct l)
  apply (simp add:arr_query_def)
  apply (simp(no_asm_simp))
  apply (case_tac "i = 0")
  apply (metis append_Cons drop_0 findex_append_nil nth_Cons_0 self_append_conv2 take_0 arr_query_def)
  by (simp add: findex_c_c findex_c_e)
lemma findex_e_c:"(\<And>i h p. i < length l \<Longrightarrow> \<not> 128 < hd (l[i]) \<Longrightarrow> findex l p [] h[i] = e_findex_line (l[i]) (p @ take i l @ drop (Suc i) l) h) \<Longrightarrow>
       i < Suc (length l) \<Longrightarrow>
       \<not> 128 < hd ((a # l)[i]) \<Longrightarrow> 128 < hd a \<Longrightarrow> findex l (p @ [a]) [c_findex_line a (p @ l) h] h[i] = e_findex_line ((a # l)[i]) (p @ take i (a # l) @ drop i l) h"
  apply (case_tac "i = 0")
  apply (simp add:arr_query_def)
  by (metis (no_types, lifting) append.assoc append_Cons append_Nil findex_append_nil less_Suc_eq_0_disj nth_Cons_Suc take_Suc_Cons arr_query_def)
lemma findex_e_e:"(\<And>i h p. i < length l \<Longrightarrow> \<not> 128 < hd (l[i]) \<Longrightarrow> findex l p [] h[i] = e_findex_line (l[i]) (p @ take i l @ drop (Suc i) l) h) \<Longrightarrow> i < Suc (length l) \<Longrightarrow> \<not> 128 < hd ((a # l)[i]) \<Longrightarrow>
       \<not> 128 < hd a \<Longrightarrow> findex l (p @ [a]) [e_findex_line a (p @ l) h] h[i] = e_findex_line ((a # l)[i]) (p @ take i (a # l) @ drop i l) h"
  apply (case_tac "i = 0")
  apply (metis append.right_neutral append_Cons append_assoc drop_0 findex_append_nil nth_Cons_0 take_0 arr_query_def)
  by (smt append.assoc append_Cons findex_append_nil less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc self_append_conv2 take_Suc_Cons arr_query_def)
lemma findex_e:"\<And>i h p. \<lbrakk>i < length l ; \<not> hd (l[i]) > 128\<rbrakk> \<Longrightarrow>  (findex l p [] h)[i] = e_findex_line (l[i]) (p@(take i l)@(drop (i+1) l)) h" 
  apply(induct l)
  apply simp
  by (simp add:findex_e_c findex_e_e)
(*findex*)

(*sindex*)
(*English*)
primrec e_sindex_l::"nat list \<Rightarrow> nat list \<Rightarrow> nat list list\<Rightarrow> (nat list \<times> string hashtrie) list \<Rightarrow> (string hashtrie) list list \<Rightarrow> (nat list \<times> string hashtrie) list "
  where"e_sindex_l [] p ks s h = (let i = (case e_common_pre_suf p ks of None \<Rightarrow> ([], Trie None [])|
                                                            Some n \<Rightarrow> (n,the (find_prefix n h))) 
                                      in (butlast s@[i]))"|
       "e_sindex_l (x#xs) p ks s h = e_sindex_l xs (p@[x]) ks (s@[([], Trie None [])]) h"
definition e_sindex_line::"nat list \<Rightarrow> nat list list  \<Rightarrow> (string hashtrie) list list \<Rightarrow> (nat list \<times> string hashtrie) list"
  where "e_sindex_line k ks h = (case k of x#s#xs \<Rightarrow> e_sindex_l  xs [s] ks [([], Trie None []),([], Trie None [])] h)"
(*English*)
(*Chinese*)
fun c_sindex_l::"nat list \<Rightarrow> nat list \<Rightarrow> nat list list \<Rightarrow> (nat list \<times> string hashtrie) list  
          => (string hashtrie) list list \<Rightarrow> (nat list \<times> string hashtrie) list "
  where "c_sindex_l [] p ks s h = (let i = (case c_common_pre_suf p ks of None \<Rightarrow> ([], Trie None [])|
                                                             Some n \<Rightarrow> (n,the (find_prefix n h))) 
                                      in (butlast s@[i]))"|
        "c_sindex_l (x#m#xs) p ks s h = c_sindex_l xs (p@[x,m]) ks (s@[([], Trie None []),([], Trie None [])]) h"
definition c_sindex_line::"nat list \<Rightarrow> nat list list  \<Rightarrow> (string hashtrie) list list \<Rightarrow> (nat list \<times> string hashtrie) list"
  where "c_sindex_line k ks h = (case k of x#s#n#m#xs \<Rightarrow>
                                  c_sindex_l  xs [n,m] ks [([], Trie None []),([], Trie None []),([], Trie None []),([], Trie None [])] h)"
(*Chinese*)
primrec sindex::"nat list list \<Rightarrow> nat list list \<Rightarrow> (nat list \<times> string hashtrie) list list  \<Rightarrow> (string hashtrie) list list \<Rightarrow> (nat list \<times> string hashtrie) list list"
  where "sindex [] ks s h = s"|
        "sindex (x#xs) ks s h =(let l = (if (hd x) > 128 then (s@[(c_sindex_line x (ks@xs) h)])
                                               else  (s@[(e_sindex_line x (ks@xs) h)])) in sindex xs (ks@[x]) l h)"
(*sindex*)


(*----------------------------------------Functional Multi Pattern Matching----------------------------------------*)
primrec kw_n:: "nat list \<Rightarrow>  nat list list \<Rightarrow> nat \<Rightarrow> nat option"
  where"kw_n p [] n = None"|
       "kw_n p (x#xs) n = (if (take (length p) x) = p then Some n else kw_n p xs (Suc n))"
value "kw_n [2,3] kw3 0"
(*Chinese*)
fun c_FMPM ::"nat list \<Rightarrow> nat list \<Rightarrow> nat list list \<Rightarrow> string hashtrie  \<Rightarrow> (nat list \<times> string hashtrie) list list \<Rightarrow> 
             (nat list \<times> string hashtrie) list list \<Rightarrow> string list \<Rightarrow> nat list \<Rightarrow> (nat list \<times> string list)"
where
      "c_FMPM [] pre ks ht s f p ps =  (case ht of Trie (Some v) _ \<Rightarrow> (ps, (p@[v])) |
                                                  Trie None _ \<Rightarrow> (ps, p))" |
      "c_FMPM (x#[]) pre ks ht s f p ps = (case ht of Trie (Some v) _ \<Rightarrow> (ps, (p@[v])) |
                                                  Trie None _ \<Rightarrow> (ps, p))" |
      "c_FMPM (x#n#xs) pre ks ht s f p ps =  (let kn = the (kw_n pre ks 0)
          in (case (value ht) of Some v \<Rightarrow>
  (let (s_m, s_ht) = s[kn][(length pre - 1)]; s_pre = drop (length pre - length s_m) pre 
in(if length s_m > 0 \<and> length s_m < length pre then c_FMPM (x#n#xs) s_pre ks s_ht s f (p@[v]) ps
                                                       else (ps, (p@[v]))))|
                            None \<Rightarrow> (case find_p [x,n] ht of None \<Rightarrow> 
              (let (f_m, f_ht) = f[kn][(length pre)]; f_pre = drop (length pre - length f_m) pre
              in (if  length f_m > 0 \<and> length f_m < length pre then c_FMPM (x#n#xs) f_pre ks f_ht s f p ps
else (ps, p)))|
                                               Some ht' \<Rightarrow> c_FMPM xs (pre@[x,n]) ks ht' s f p (ps@[x,n]))))"
lemma c_FMPM_value_append:"\<And>ps. fst (c_FMPM c_ts pre ks ht s f p (ps@pa)) = ps@(fst (c_FMPM c_ts pre ks ht s f p pa))"
  apply (induct c_ts pre ks ht s f p pa  rule:c_FMPM.induct)
  apply (simp,split hashtrie.split,split option.split,rule allI,rule conjI)
  apply auto[1]
  apply (rule allI)
   apply auto[1]
   apply (simp,split hashtrie.split,split option.split,rule allI,rule conjI)
   apply auto[1]
   apply auto[1]
   apply (simp(no_asm_simp))
   apply (simp(no_asm_simp) only:Let_def,split option.split,rule conjI)
   apply (rule impI,split option.split,rule conjI)
   apply (rule impI,split prod.split,rule allI,rule allI,rule impI,split if_split,rule conjI)
   apply (rule impI)
   using old.prod.case option.simps(4) apply auto[1]
   apply (rule impI)
   using old.prod.case option.simps(4) apply auto[1]
   apply (rule allI,rule impI)
   using old.prod.case option.simps(4) apply auto[1]
   apply (rule allI,rule impI,split prod.split,rule allI,rule allI,rule impI,split if_split,rule conjI)
   apply (rule impI)
   using old.prod.case option.simps(4) apply auto[1]
   apply (rule impI)
using old.prod.case option.simps(4) apply auto[1]
  done
lemma c_FMPM_length:"length (fst (c_FMPM c_ts pre ks ht s f p ps)) \<ge> length ps"
  apply (induct c_ts pre ks ht s f p ps rule:c_FMPM.induct)
  apply (simp,split hashtrie.split,split option.split,rule allI,rule conjI)
  apply auto[1]
  apply (rule allI)
  apply auto[1]
  apply (simp,split hashtrie.split,split option.split,rule allI,rule conjI)
  apply auto[1]
  apply (rule allI)
  apply auto[1]
  apply (simp(no_asm_simp))
  apply (simp(no_asm_simp) only:Let_def,split option.split,rule conjI)
  apply (rule impI,split option.split,rule conjI)
  apply (rule impI,split prod.split,rule allI,rule allI,rule impI,split if_split,rule conjI)
  apply (rule impI)
  apply presburger
  apply (rule impI)
  apply simp
  apply (rule allI,rule impI)
  using add_Suc_right le_SucI length_append apply force
  apply (rule allI,rule impI,split prod.split,rule allI,rule allI,rule impI,split if_split,rule conjI)
  apply (rule impI)
  apply presburger
  apply (rule impI)
  apply simp
  done
(*English*)
fun e_FMPM::"nat list \<Rightarrow> nat list \<Rightarrow> nat list list \<Rightarrow> string hashtrie  \<Rightarrow> (nat list \<times> string hashtrie) list list \<Rightarrow> 
            (nat list \<times> string hashtrie) list list \<Rightarrow> string list \<Rightarrow> nat list \<Rightarrow> (nat list \<times> string list)"
where "e_FMPM [] pre ks ht s f p ps =  (case ht of Trie (Some v) _ \<Rightarrow> (ps, (p@[v])) |
                                                  Trie None _ \<Rightarrow> (ps, p))" |
      "e_FMPM (x#xs) pre ks ht s f p ps = (let kn = the (kw_n pre ks 0)
               in (case (value ht) of (Some v) \<Rightarrow> 
(let (s_m, s_ht) = s[kn][(length pre - 1)]; s_pre = drop (length pre - length s_m) pre 
                    in(if s_m \<noteq> [] \<and> length s_m < length pre then e_FMPM (x#xs) s_pre ks s_ht s f (p@[v]) ps
                                                         else (ps, (p@[v]))))|
                                  None \<Rightarrow> (case find_p [x] ht of None \<Rightarrow> 
                     (let (f_m, f_ht) = f[kn][(length pre)]; f_pre = drop (length pre - length f_m) pre
                     in (if f_m \<noteq> [] \<and> length f_m < length pre 
then e_FMPM (x#xs) f_pre ks f_ht s f p ps else (ps, p)))|
                                                           Some ht' \<Rightarrow> 
e_FMPM xs (pre@[x]) ks ht' s f p (ps@[x])) ))"
lemma e_FMPM_append:"\<And>ps. fst (e_FMPM c_ts pre ks ht s f p (ps@pa)) =  ps@(fst (e_FMPM c_ts pre ks ht s f p pa))"
  apply (induct c_ts pre ks ht s f p pa  rule:e_FMPM.induct)
  apply (simp,split hashtrie.split,split option.split,rule allI,rule conjI)
  apply auto[1]
  apply (rule allI)
  apply auto[1]
  apply (simp(no_asm_simp))
  apply (simp(no_asm_simp) only:Let_def,split option.split,rule conjI)
  apply (rule impI,split option.split,rule conjI)
  apply (rule impI,split prod.split,rule allI,rule allI,rule impI,split if_split,rule conjI)
  apply (rule impI)
  using old.prod.case option.simps(4) apply auto[1]
  apply (rule impI)
  using old.prod.case option.simps(4) apply auto[1]
  apply (rule allI,rule impI)
  using add_Suc_right le_SucI length_append apply force
  apply (rule allI,rule impI,split prod.split,rule allI,rule allI,rule impI,split if_split,rule conjI)
  apply (rule impI)
  using old.prod.case option.simps(4) apply auto[1]
  apply (rule impI)
  using old.prod.case option.simps(4) apply auto[1]
  done
lemma e_FMPM_length:"length (fst (e_FMPM c_ts pre ks ht s f p ps)) \<ge> length ps"
  apply (induct c_ts pre ks ht s f p ps rule:e_FMPM.induct)
  apply (simp,split hashtrie.split,split option.split,rule allI,rule conjI)
  apply auto[1]
  apply (rule allI)
  apply auto[1]
  apply (simp(no_asm_simp))
  apply (simp(no_asm_simp) only:Let_def,split option.split,rule conjI)
  apply (rule impI,split option.split,rule conjI)
  apply (rule impI,split prod.split,rule allI,rule allI,rule impI,split if_split,rule conjI)
  apply (rule impI)
  apply presburger
  apply (rule impI)
apply simp
  apply (rule allI,rule impI)
  using add_Suc_right le_SucI length_append apply force
  apply (rule allI,rule impI,split prod.split,rule allI,rule allI,rule impI,split if_split,rule conjI)
  apply (rule impI)
  apply presburger
  apply (rule impI)
  apply simp
  done
fun FMPM::"nat list \<Rightarrow> nat list list \<Rightarrow>string hashtrie list list  \<Rightarrow> string list \<Rightarrow> string list"
  where"FMPM [] ks h p = p"|
       "FMPM (x#xs) ks h p = (if x>128 \<and> length xs \<ge> 3 
                           then (case xs of (xx#a#aa#as) \<Rightarrow> 
                                    (case find_p [a,aa] (h[x][xx]) of None \<Rightarrow> FMPM (a#aa#as) ks h p|
                                                             Some ht \<Rightarrow> 
                             (let (i, n_p) = c_FMPM as [x,xx,a,aa] ks ht (sindex ks [] [] h) (findex ks [] [] h) p []
                             in ( FMPM (drop (length i) as) ks h n_p))))
                            else (if x>128 \<and> length xs < 3 then p 
                                                       else (case xs of [] \<Rightarrow> p|
                                                             xx#as \<Rightarrow> (case find_p [xx] (h!x!x) of None \<Rightarrow>
                                                                      FMPM xs ks h p |
                                                                                        Some ht \<Rightarrow>
                                  (let (i, n_p) = e_FMPM as [x,xx] ks ht (sindex ks [] [] h) (findex ks [] [] h) p []
                                  in (FMPM (drop (length i) (as)) ks h n_p))))))"

end
