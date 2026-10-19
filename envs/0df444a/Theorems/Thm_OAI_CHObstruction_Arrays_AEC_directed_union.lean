-- Prove2me | Theorems.Thm_OAI_CHObstruction_Arrays_AEC_directed_union
-- name    : OAI.CHObstruction.Arrays.AEC.directed_union
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:20:29.611051+00:00
-- url     : https://prove2.me/theorems/28629878-9c86-4439-ad0f-ff3a49bb2a78
-- title:
--   Directed systems in the array class have a union that is a least strong upper bound
-- statement:
--   Assume CH, $2^{\aleph_0}=\aleph_1$. Let $\mathcal C$ (the *palette*) be the set of binary sequences $a:\mathbb N\to\{0,1\}$ modulo the equivalence relation of differing in only finitely many places, and write $[a]\in\mathcal C$ for the class of $a$. For a set $I$, $\mathrm{Tup}(I)$ is the set of *tuples* in $I$, i.e. injective maps $t:\{0,\dots,n\}\to I$ with $n\in\mathbb N$ (of length $n+1$); for a strictly increasing $e:\{0,\dots,m\}\to\{0,\dots,n\}$ the tuple $t\circ e$ is a *subtuple* of $t$, and an injection $h:I\to I'$ sends $t$ to $h\circ t\in\mathrm{Tup}(I')$.
--
--   For a coloring $c:\mathrm{Tup}(I)\to\mathcal C$ and a tuple $t$ of length $n+1$, the *diagram test* $\mathsf T(c,t)$ asserts that there is a diagram $d$ on $\{0,\dots,n\}$ (two relations $\equiv_d$, $\triangleleft_d$ on labels $(F,k)$, where $F\subseteq\{0,\dots,n\}$ is finite nonempty and $k\in\mathbb N$, together with countable-ordinal tags) such that for every strictly increasing $e:\{0,\dots,m\}\to\{0,\dots,n\}$ the restricted diagram $d|_e$ is valid and $\mathrm{code}(m,d|_e)=c(t\circ e)$. Here *valid* means that $\equiv_d$ is an equivalence relation compatible with $\triangleleft_d$ and the tags, tags strictly increase along $\triangleleft_d$, labels with the same $\triangleleft_d$-predecessors are equivalent, and the root labels $(\{a\},0)$ of distinct points are inequivalent; $\mathrm{code}$ is a fixed injection of diagrams on finite sets into $\mathcal C$, which exists under CH. In particular $\mathsf T(c,t)$ depends only on the colors $c(t\circ e)$ of the subtuples of $t$.
--
--   An *array* $M$ consists of a nonempty set $I_M$ of *indices*, a nonempty set $B_M$ of *base points* carrying a dense linear order without endpoints in which every closed interval is countable, and a *bit matrix* $\beta_M:\mathrm{Tup}(I_M)\times\mathbb N\times B_M\to\{0,1\}$. The set $\mathrm{Pts}(M)$ of *points* of $M$ is the disjoint union of six sorts: index points $i\in I_M$; base points $b\in B_M$; group points $s$, one for each finite $s\subseteq B_M$; star points $v$, one for each finite $v\subseteq\mathbb N$; row points $(t,n,s)$ with $t\in\mathrm{Tup}(I_M)$, $n\in\mathbb N$ and finite $s\subseteq B_M$; and column points $(t,b,v)$ with $t\in\mathrm{Tup}(I_M)$, $b\in B_M$ and finite $v\subseteq\mathbb N$. The *column color* of $t\in\mathrm{Tup}(I_M)$ at $b\in B_M$ is $\chi_M(t,b)=[\,n\mapsto\beta_M(t,n,b)\,]\in\mathcal C$, and $M$ is an *object* if for every $t\in\mathrm{Tup}(I_M)$ only countably many $b\in B_M$ fail the test $\mathsf T(\chi_M(\cdot,b),t)$.
--
--   A *map* $f:M\to N$ of arrays consists of an injection $f_I:I_M\to I_N$, an order embedding $f_B:B_M\to B_N$, finite *row shifts* $\rho_f(t,n)\subseteq B_N$ and finite *column shifts* $\gamma_f(t,b)\subseteq\mathbb N$ ($t\in\mathrm{Tup}(I_M)$, $n\in\mathbb N$, $b\in B_M$) satisfying the bit identity
--   $$\beta_N(f_I\circ t,n,f_Bb)\oplus[f_Bb\in\rho_f(t,n)]\oplus[n\in\gamma_f(t,b)]=\beta_M(t,n,b),$$
--   where $\oplus$ is exclusive or and $[\,\cdot\,]\in\{0,1\}$ is the truth value of a statement. A map $f$ acts on points by $\hat f(i)=f_I(i)$, $\hat f(b)=f_B(b)$, $\hat f(s)=f_B[s]$ on group points, $\hat f(v)=v$ on star points,
--   $$\hat f(t,n,s)=\bigl(f_I\circ t,\ n,\ \rho_f(t,n)\mathbin{\triangle}f_B[s]\bigr),\qquad \hat f(t,b,v)=\bigl(f_I\circ t,\ f_Bb,\ \gamma_f(t,b)\mathbin{\triangle}v\bigr)$$
--   on row and column points, where $\triangle$ is symmetric difference; the point map $\hat f$ is always injective. For a map $f:M\to N$, a tuple $t\in\mathrm{Tup}(I_M)$ and a base point $b\in B_N$ of the target, the *twisted color* is
--   $$\chi_f(t,b)=\bigl[\,n\mapsto\beta_N(f_I\circ t,n,b)\oplus[b\in\rho_f(t,n)]\,\bigr]\in\mathcal C .$$ A map $f:M\to N$ is *strong* if the range of $f_B$ is order-convex in $B_N$ (whenever $f_Ba\le z\le f_Bc$, also $z\in f_B[B_M]$) and $\mathsf T(\chi_f(\cdot,b),t)$ holds for every $t\in\mathrm{Tup}(I_M)$ and every $b\in B_N$ outside the range of $f_B$.
--
--   The signature $L$ of arrays is countable and relational. Its symbols are: unary predicates for the six sorts of points; for $k,n\in\mathbb N$ a unary predicate for the row points $(t,n,s)$ whose tuple has length $k+1$, and one for the column points whose tuple has length $k+1$; for each finite $w\subseteq\mathbb N$ a unary predicate true only of the star point $w$; projection relations linking a row point $(t,n,s)$ to the index points $t(0),\dots,t(k)$, and a column point $(t,b,v)$ to the base point $b$ and to $t(0),\dots,t(k)$; the strict order $a<b$ of base points; incidence between a base point $b$ and a group point $s$ with $b\in s$; the bit relation between a row point $(t,n,s)$ and a column point $(t,b,v)$ with the same tuple, true when $\beta_M(t,n,b)\oplus[b\in s]\oplus[n\in v]=1$; the ternary relations $w=s\mathbin{\triangle}s'$ on group points and on star points; and the action relations $\bigl((t,n,s),u,(t,n,s\mathbin{\triangle}u)\bigr)$ of group points on row points and $\bigl((t,b,v),w,(t,b,v\mathbin{\triangle}w)\bigr)$ of star points on column points. Every array $M$ is in this way an $L$-structure on $\mathrm{Pts}(M)$ (its *basic relations*).
--
--   An $L$-structure $R$ consists of a set $|R|$ (in the cumulative hierarchy of pure sets) and an $n$-ary relation on $|R|$ for each $n$-ary symbol. $R$ is a *substructure* of $T$ if $|R|\subseteq|T|$ and the relations of $R$ are the restrictions of those of $T$. A *presentation* of $R$ is an array $M$ with a bijection $\pi:\mathrm{Pts}(M)\to|R|$ carrying the basic relations of $M$ onto the relations of $R$. Let $\mathbb K$ be the class of $L$-structures having a presentation by an object, and write $R\le_{\mathbb K}T$ if there are presentations $(M,\pi)$ of $R$ and $(N,\sigma)$ of $T$ by objects and a strong map $f:M\to N$ realizing the inclusion, $\sigma(\hat f(x))=\pi(x)$ for all $x\in\mathrm{Pts}(M)$.
--
--   **Theorem.** Let $J$ be a nonempty directed preordered set and let $(F_i)_{i\in J}$ be $L$-structures in $\mathbb K$ with $F_i\le_{\mathbb K}F_j$ whenever $i\le j$. Then there is an $L$-structure $U$ such that
--   1. $U\in\mathbb K$;
--   2. $U$ is the union of the $F_i$: each $F_i$ is a substructure of $U$, and every element of $|U|$ lies in some $|F_i|$;
--   3. $F_i\le_{\mathbb K}U$ for every $i\in J$;
--   4. $U$ is least: if $N\in\mathbb K$ and $F_i\le_{\mathbb K}N$ for all $i$, then $U\le_{\mathbb K}N$.
--
--   In particular
--
--   $$
--   |U|=\bigcup_{i\in J}|F_i|,\qquad F_i\le_{\mathbb K}U\ \ (i\in J),\qquad \bigl(\forall i:\ F_i\le_{\mathbb K}N\bigr)\ \Rightarrow\ U\le_{\mathbb K}N\ \ (N\in\mathbb K).
--   $$
--
--   Taking for $J$ a nonzero ordinal gives the chain-union axiom of an abstract elementary class for $(\mathbb K,\le_{\mathbb K})$: unions of nonempty chains exist in the class, are strong upper bounds, and are least among strong upper bounds.
--
--   **Formalization Note** $L$-structures are `RelModel Language`, whose universe is a `ZFSet`; $\mathbb K$ and $\le_{\mathbb K}$ are the fields `objects` and `strong` of `classData hCH`, abbreviated `Object` and `Strong`; item 2 is `RelModel.IsUnion F U`. The index type $J$ lives in the same universe as the sets.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/AEC.lean#L327-L402

import Mathlib
import Definitions.Def_CHObstruction
import Definitions.Def_OAI_ModelTheory_Categoricity_Collapse
import Definitions.Def_OAI_ModelTheory_Categoricity_Diagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_Partition
import Definitions.Def_OAI_ModelTheory_Categoricity_Colors
import Definitions.Def_OAI_ModelTheory_Categoricity_EndpointDiagrams
import Definitions.Def_OAI_ModelTheory_Categoricity_TailBound
import Definitions.Def_OAI_ModelTheory_Categoricity_Arrays
import Definitions.Def_OAI_ModelTheory_Categoricity_ArrayMaps
import Definitions.Def_OAI_ModelTheory_Categoricity_ArrayEmbeddings
import Definitions.Def_OAI_ModelTheory_Categoricity_Subarrays
import Definitions.Def_OAI_ModelTheory_Categoricity_ArrayIsomorphisms
import Definitions.Def_OAI_ModelTheory_Categoricity_DirectedLimits
import Definitions.Def_OAI_ModelTheory_Categoricity_AEC

open OAI OAI.CHObstruction OAI.CHObstruction.Arrays OAI.CHObstruction.Arrays.AEC
universe u v w
open Cardinal Ordinal Order
open Tuples
variable {M N : Data.{u}}
variable (hCH : CH.{u})
variable {hCH : CH.{u}}

theorem OAI.CHObstruction.Arrays.AEC.directed_union {J : Type u} [Preorder J] [IsDirectedOrder J] [Nonempty J]
    (F : J → RelModel.{u} Language) (ho : ∀ i, Object (hCH := hCH) (F i))
    (hs : ∀ i j, i ≤ j → Strong (hCH := hCH) (F i) (F j)) :
    ∃ U, Object (hCH := hCH) U ∧ RelModel.IsUnion F U ∧
      (∀ i, Strong (hCH := hCH) (F i) U) ∧
      (∀ N, Object (hCH := hCH) N → (∀ i, Strong (hCH := hCH) (F i) N) → Strong (hCH := hCH) U N) := by sorry
