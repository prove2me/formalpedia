-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Reduction_scoreMax_recentered
-- name    : OAI.GaussianPropeller.Reduction.scoreMax_recentered
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T05:58:35.841586+00:00
-- url     : https://prove2.me/theorems/e4fdc482-4b6d-45ba-aeac-83e732de662e
-- title:
--   Score maximum of a recentred tuple
-- statement:
--   Let $k\ge2$ and $z_1,\dots,z_k\in\mathbb R^d$ with $\sum_jz_j=0$, and let $z'$ be the tuple obtained by deleting $z_i$ and adding $\frac{z_i}{k-1}$ to every other vector. Then for every $x$,
--   $$
--   \max_j\langle z'_j,x\rangle=\max_{j\ne i}\langle z_j,x\rangle+\frac{\langle z_i,x\rangle}{k-1}.
--   $$
--
--   The zero vector in slot $i$ never wins strictly, because the other recentred scores sum to zero.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Deletion.lean#L96-L126

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

theorem OAI.GaussianPropeller.Reduction.scoreMax_recentered (hk : 2 ≤ k) (z : Fin k → Space d)
    (hz : ∑ j, z j = 0) (i : Fin k) (x : Space d) :
    scoreMax (recentered z i).ofLp x = omittedMax hk z i x + ⟪((k:ℝ)-1)⁻¹ • z i,x⟫ := by sorry
