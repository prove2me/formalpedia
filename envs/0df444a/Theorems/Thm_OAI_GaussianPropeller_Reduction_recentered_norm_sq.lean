-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Reduction_recentered_norm_sq
-- name    : OAI.GaussianPropeller.Reduction.recentered_norm_sq
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:58:00.746066+00:00
-- url     : https://prove2.me/theorems/294581be-a3d2-418c-ba64-4a76ef1a5870
-- title:
--   Norm of a recentred tuple
-- statement:
--   Let $k\ge2$ and $z_1,\dots,z_k\in\mathbb R^d$ with $\sum_jz_j=0$. Fix $i$, and let $z'$ be the tuple with $z'_i=0$ and $z'_j=z_j+\frac{z_i}{k-1}$ for $j\ne i$. Then
--   $$
--   |z'|^2=\sum_j|z_j|^2-\frac{k}{k-1}\,|z_i|^2 .
--   $$
--
--   Deleting a cell and redistributing its centroid evenly loses exactly this much squared length.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Deletion.lean#L61-L94

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
variable {d k : ℕ} [NeZero k]

omit [NeZero k] in
theorem OAI.GaussianPropeller.Reduction.recentered_norm_sq (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) :
    ‖recentered z i‖^2 = (∑ j, ‖z j‖^2) -
      ((k:ℝ)/((k:ℝ)-1)) * ‖z i‖^2 := by sorry
