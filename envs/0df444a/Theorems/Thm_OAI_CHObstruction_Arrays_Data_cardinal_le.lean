-- Prove2me | Theorems.Thm_OAI_CHObstruction_Arrays_Data_cardinal_le
-- name    : OAI.CHObstruction.Arrays.Data.cardinal_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T03:07:45.176421+00:00
-- url     : https://prove2.me/theorems/9be6bb34-bab7-469a-b2fd-cfd8e6a41cd1
-- title:
--   An array whose index set and base have size at most $\kappa$ has at most $\kappa$ points
-- statement:
--   For a set $I$, $\mathrm{Tup}(I)$ is the set of *tuples* in $I$, i.e. injective maps $t:\{0,\dots,n\}\to I$ with $n\in\mathbb N$ (of length $n+1$); for a strictly increasing $e:\{0,\dots,m\}\to\{0,\dots,n\}$ the tuple $t\circ e$ is a *subtuple* of $t$, and an injection $h:I\to I'$ sends $t$ to $h\circ t\in\mathrm{Tup}(I')$.
--
--   An *array* $M$ consists of a nonempty set $I_M$ of *indices*, a nonempty set $B_M$ of *base points* carrying a dense linear order without endpoints in which every closed interval is countable, and a *bit matrix* $\beta_M:\mathrm{Tup}(I_M)\times\mathbb N\times B_M\to\{0,1\}$. The set $\mathrm{Pts}(M)$ of *points* of $M$ is the disjoint union of six sorts: index points $i\in I_M$; base points $b\in B_M$; group points $s$, one for each finite $s\subseteq B_M$; star points $v$, one for each finite $v\subseteq\mathbb N$; row points $(t,n,s)$ with $t\in\mathrm{Tup}(I_M)$, $n\in\mathbb N$ and finite $s\subseteq B_M$; and column points $(t,b,v)$ with $t\in\mathrm{Tup}(I_M)$, $b\in B_M$ and finite $v\subseteq\mathbb N$.
--
--   **Theorem.** Let $M$ be an array and let $\kappa$ be an infinite cardinal with $|I_M|\le\kappa$ and $|B_M|\le\kappa$. Then
--
--   $$
--   |\mathrm{Pts}(M)|\le\kappa .
--   $$
--
--   The points of an array are the elements of the relational structure it presents, so this bound controls the size of the structures in the class built from arrays; it supplies the cardinality estimate in the downward Löwenheim–Skolem step for subarrays.
--
--   **Formalization Note** $\mathrm{Pts}(M)$ is `M.Carrier`, the inductive type `Point M.I M.B`. The bit matrix and the order of the base play no role in the bound.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/ModelTheory/Categoricity/Subarrays.lean#L134-L155

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

open OAI OAI.CHObstruction OAI.CHObstruction.Arrays
universe u v w
open Cardinal Ordinal Order
open Tuples
open scoped symmDiff
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqB_15
attribute [local instance] OAI.CHObstruction.Arrays.instDecidableEqElemB
variable (M : Data.{u})
variable {M}
variable (J : Set M.I) (S : Set M.B) [Nonempty J] [Nonempty S]
  [DenselyOrdered S] [NoMinOrder S] [NoMaxOrder S]

theorem OAI.CHObstruction.Arrays.Data.cardinal_le (κ : Cardinal.{u}) (hκ : ℵ₀ ≤ κ)
    (hI : #M.I ≤ κ) (hB : #M.B ≤ κ) : #M.Carrier ≤ κ := by sorry
