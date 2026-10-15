-- Prove2me | Theorems.Thm_OAI_DoublingHilbert_isCompact_exists_packing_bound
-- name    : OAI.DoublingHilbert.isCompact_exists_packing_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-14T22:47:28.52939+00:00
-- url     : https://prove2.me/theorems/0e843811-55ce-45e4-bf9d-6afc858a4474
-- title:
--   Compact sets admit a uniform bound on the size of $r$-separated families
-- statement:
--   Let $(X,d)$ be a pseudometric space, let $K\subseteq X$ be a compact set and let $r>0$. Then there is a natural number $N$, depending only on $K$ and $r$, such that every finite $r$-separated family of points of $K$ has at most $N$ members: for every $n\in\mathbb{N}$ and all points $z_1,\dots,z_n\in K$,
--
--   $$
--   d(z_i,z_j)\ge r\ \text{ for all } i\ne j \quad\Longrightarrow\quad n\le N .
--   $$
--
--   In other words, the $r$-packing number of a compact set is finite for every positive separation $r$. In the nonembedding argument for the doubling subset of Hilbert space, this is applied to a closed ball of a finite-dimensional space (which is compact) to rule out arbitrarily large $1$-separated families inside it.
--
--   **Formalization Note** Families are maps `z : Fin n → X`; they are not required to be injective, since separation at distinct indices together with $r>0$ already forces distinct points.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Doubling.lean#L100-L126

import Mathlib
import Definitions.Def_DoublingHilbert
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling

open OAI OAI.DoublingHilbert
open MeasureTheory Set Filter
open scoped BigOperators Topology
open Set
open Set Metric

theorem OAI.DoublingHilbert.isCompact_exists_packing_bound {X : Type*} [PseudoMetricSpace X]
    {s : Set X} (hs : IsCompact s) {r : ℝ} (hr : 0 < r) :
    ∃ bound : ℕ, ∀ {n : ℕ} (z : Fin n → X), (∀ i, z i ∈ s) →
      (∀ i j, i ≠ j → r ≤ dist (z i) (z j)) → n ≤ bound := by sorry
