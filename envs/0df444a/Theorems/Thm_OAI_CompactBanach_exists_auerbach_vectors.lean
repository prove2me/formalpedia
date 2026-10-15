-- Prove2me | Theorems.Thm_OAI_CompactBanach_exists_auerbach_vectors
-- name    : OAI.CompactBanach.exists_auerbach_vectors
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T07:05:22.35943+00:00
-- url     : https://prove2.me/theorems/aa4e5bac-5266-4ae9-be0e-fdf39b40c295
-- title:
--   Every infinite-dimensional normed space contains Auerbach systems of every finite size
-- statement:
--   Let $B$ be a real normed space that is not finite-dimensional (completeness is not assumed), and let $\iota$ be a finite index set. Then there are vectors $(v_i)_{i\in\iota}$ in $B$ with $\|v_i\|\le1$ for every $i\in\iota$ such that for every family of real coefficients $(c_j)_{j\in\iota}$ and every index $i\in\iota$,
--   $$
--   |c_i|\le\Bigl\|\sum_{j\in\iota}c_j\,v_j\Bigr\| .
--   $$
--
--   Taking $c$ to be the indicator of a single index shows that each $v_i$ is a unit vector, and the inequality implies that the $v_i$ are linearly independent. Combined with the triangle inequality it gives $\max_i|c_i|\le\|\sum_j c_jv_j\|\le\sum_j|c_j|$, so $c\mapsto\sum_j c_jv_j$ is a linear isomorphism from $\mathbb{R}^{\iota}$ onto its image with explicit constants. Such a system is used to copy finitely many coordinates of $\ell^2$ into an arbitrary infinite-dimensional normed space.
--
--   **Formalization Note** The finiteness of the index type is a `Fintype ι` instance and infinite-dimensionality is the hypothesis `¬ FiniteDimensional ℝ B`; the sum runs over all of `ι`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Geometry/DoublingHilbert/Auerbach.lean#L70-L93

import Mathlib
import Definitions.Def_CompactBanach
import Definitions.Def_OAI_Geometry_DoublingHilbert_Construction
import Definitions.Def_OAI_Geometry_DoublingHilbert_Derivatives
import Definitions.Def_OAI_Geometry_DoublingHilbert_Integration
import Definitions.Def_OAI_Geometry_DoublingHilbert_Rectangles
import Definitions.Def_OAI_Geometry_DoublingHilbert_Grids
import Definitions.Def_OAI_Geometry_DoublingHilbert_SelectedSheets
import Definitions.Def_OAI_Geometry_DoublingHilbert_Energy
import Definitions.Def_OAI_Geometry_DoublingHilbert_Crossings
import Definitions.Def_OAI_Geometry_DoublingHilbert_Doubling

open OAI OAI.CompactBanach
open Set Metric
open scoped BigOperators

theorem OAI.CompactBanach.exists_auerbach_vectors {B ι : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [Fintype ι] (hB : ¬ FiniteDimensional ℝ B) :
    ∃ v : ι → B, (∀ i, ‖v i‖ ≤ 1) ∧
      ∀ (c : ι → ℝ) i, |c i| ≤ ‖∑ j, c j • v j‖ := by sorry
