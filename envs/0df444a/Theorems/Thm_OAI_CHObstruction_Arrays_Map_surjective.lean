-- Prove2me | Theorems.Thm_OAI_CHObstruction_Arrays_Map_surjective
-- name    : OAI.CHObstruction.Arrays.Map.surjective
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:03:56.317169+00:00
-- url     : https://prove2.me/theorems/7821d2e9-b583-42b2-bd18-0e3d17b43518
-- title:
--   An array map that is onto on indices and on base points is onto on all points
-- statement:
--   For a set $I$, $\mathrm{Tup}(I)$ is the set of *tuples* in $I$, i.e. injective maps $t:\{0,\dots,n\}\to I$ with $n\in\mathbb N$ (of length $n+1$); for a strictly increasing $e:\{0,\dots,m\}\to\{0,\dots,n\}$ the tuple $t\circ e$ is a *subtuple* of $t$, and an injection $h:I\to I'$ sends $t$ to $h\circ t\in\mathrm{Tup}(I')$.
--
--   An *array* $M$ consists of a nonempty set $I_M$ of *indices*, a nonempty set $B_M$ of *base points* carrying a dense linear order without endpoints in which every closed interval is countable, and a *bit matrix* $\beta_M:\mathrm{Tup}(I_M)\times\mathbb N\times B_M\to\{0,1\}$. The set $\mathrm{Pts}(M)$ of *points* of $M$ is the disjoint union of six sorts: index points $i\in I_M$; base points $b\in B_M$; group points $s$, one for each finite $s\subseteq B_M$; star points $v$, one for each finite $v\subseteq\mathbb N$; row points $(t,n,s)$ with $t\in\mathrm{Tup}(I_M)$, $n\in\mathbb N$ and finite $s\subseteq B_M$; and column points $(t,b,v)$ with $t\in\mathrm{Tup}(I_M)$, $b\in B_M$ and finite $v\subseteq\mathbb N$.
--
--   A *map* $f:M\to N$ of arrays consists of an injection $f_I:I_M\to I_N$, an order embedding $f_B:B_M\to B_N$, finite *row shifts* $\rho_f(t,n)\subseteq B_N$ and finite *column shifts* $\gamma_f(t,b)\subseteq\mathbb N$ ($t\in\mathrm{Tup}(I_M)$, $n\in\mathbb N$, $b\in B_M$) satisfying the bit identity
--   $$\beta_N(f_I\circ t,n,f_Bb)\oplus[f_Bb\in\rho_f(t,n)]\oplus[n\in\gamma_f(t,b)]=\beta_M(t,n,b),$$
--   where $\oplus$ is exclusive or and $[\,\cdot\,]\in\{0,1\}$ is the truth value of a statement. A map $f$ acts on points by $\hat f(i)=f_I(i)$, $\hat f(b)=f_B(b)$, $\hat f(s)=f_B[s]$ on group points, $\hat f(v)=v$ on star points,
--   $$\hat f(t,n,s)=\bigl(f_I\circ t,\ n,\ \rho_f(t,n)\mathbin{\triangle}f_B[s]\bigr),\qquad \hat f(t,b,v)=\bigl(f_I\circ t,\ f_Bb,\ \gamma_f(t,b)\mathbin{\triangle}v\bigr)$$
--   on row and column points, where $\triangle$ is symmetric difference; the point map $\hat f$ is always injective.
--
--   **Theorem.** Let $f:M\to N$ be a map of arrays such that $f_I:I_M\to I_N$ and $f_B:B_M\to B_N$ are both surjective. Then the point map is surjective:
--
--   $$
--   \hat f\bigl[\mathrm{Pts}(M)\bigr]=\mathrm{Pts}(N).
--   $$
--
--   Since $\hat f$ is injective, $f$ then induces a bijection between the point sets, and hence an isomorphism of the relational structures that the two arrays present. This is used in the categoricity argument above the tail threshold: two array objects with countable bases and index sets of the same size are connected by a map that is bijective on indices and on bases, and the theorem turns it into an isomorphism of the presented structures.
--
--   **Formalization Note** Points form the inductive type `Point I B` with constructors `index`, `base`, `group`, `star`, `row`, `col`, and $\hat f$ is `Map.onPoint f`. The bit identity plays no role in this statement.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/ArrayEmbeddings.lean#L187-L214

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

open OAI OAI.CHObstruction OAI.CHObstruction.Arrays
universe u v w
open Cardinal Ordinal Order
open Tuples
open scoped symmDiff
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_11
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_12
variable {M N : Data.{u}}

theorem OAI.CHObstruction.Arrays.Map.surjective (f : Map M N) (hi : Function.Surjective f.index)
    (hb : Function.Surjective f.base) : Function.Surjective f.onPoint := by sorry
