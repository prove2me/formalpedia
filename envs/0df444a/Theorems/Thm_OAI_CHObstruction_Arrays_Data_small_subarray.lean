-- Prove2me | Theorems.Thm_OAI_CHObstruction_Arrays_Data_small_subarray
-- name    : OAI.CHObstruction.Arrays.Data.small_subarray
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:12:34.466463+00:00
-- url     : https://prove2.me/theorems/083c20b4-ed48-41be-955f-81a465e748dd
-- title:
--   Every set of points of an array object lies in a strong subobject of size at most $|A|+\aleph_0$
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
--   on row and column points, where $\triangle$ is symmetric difference; the point map $\hat f$ is always injective.
--
--   For a map $f:M\to N$, a tuple $t\in\mathrm{Tup}(I_M)$ and a base point $b\in B_N$ of the target, the *twisted color* is
--   $$\chi_f(t,b)=\bigl[\,n\mapsto\beta_N(f_I\circ t,n,b)\oplus[b\in\rho_f(t,n)]\,\bigr]\in\mathcal C .$$ A map $f:M\to N$ is *strong* if the range of $f_B$ is order-convex in $B_N$ (whenever $f_Ba\le z\le f_Bc$, also $z\in f_B[B_M]$) and $\mathsf T(\chi_f(\cdot,b),t)$ holds for every $t\in\mathrm{Tup}(I_M)$ and every $b\in B_N$ outside the range of $f_B$.
--
--   **Theorem.** Let $M$ be an array that is an object and let $A\subseteq\mathrm{Pts}(M)$ be an arbitrary set of points. Then there are an array $N$ and a map $f:N\to M$ with
--
--   $$
--   A\subseteq\hat f\bigl[\mathrm{Pts}(N)\bigr]\qquad\text{and}\qquad|\mathrm{Pts}(N)|\le|A|+\aleph_0 ,
--   $$
--
--   such that moreover
--   1. $N$ is an object, and
--   2. $f$ is strong.
--
--   This is the downward Löwenheim–Skolem property of the class of structures presented by array objects, with Löwenheim–Skolem number $\aleph_0$: every subset of a structure in the class is contained in a strong substructure of size at most its own size plus $\aleph_0$.
--
--   **Formalization Note** The conclusion is `∃ N f, N.IsObject hCH ∧ f.Strong hCH ∧ A ⊆ Set.range f.onPoint ∧ #N.Carrier ≤ #A + ℵ₀`; the cardinal $|A|$ is that of the subtype of `M.Carrier`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/ArrayIsomorphisms.lean#L202-L245

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

open OAI OAI.CHObstruction OAI.CHObstruction.Arrays
universe u v w
open Cardinal Ordinal Order
open Tuples
open scoped symmDiff
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqI
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_19
variable {M : Data.{u}}

theorem OAI.CHObstruction.Arrays.Data.small_subarray (M : Data.{u}) (hCH : CH.{u}) (hM : M.IsObject hCH)
    (A : Set M.Carrier) :
    ∃ N : Data.{u}, ∃ f : Map N M, N.IsObject hCH ∧ f.Strong hCH ∧
      A ⊆ Set.range f.onPoint ∧ #N.Carrier ≤ #A + ℵ₀ := by sorry
