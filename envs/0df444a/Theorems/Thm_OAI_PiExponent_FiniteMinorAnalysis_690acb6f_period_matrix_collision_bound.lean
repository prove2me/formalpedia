-- Prove2me | Theorems.Thm_OAI_PiExponent_FiniteMinorAnalysis_690acb6f_period_matrix_collision_bound
-- name    : OAI.PiExponent.FiniteMinorAnalysis_690acb6f.period_matrix_collision_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:28:16.953425+00:00
-- url     : https://prove2.me/theorems/09d6e3a1-45ca-4ce8-b927-7b459e11a558
-- title:
--   Period minors lose an exponential factor for repeated transverse indices
-- statement:
--   The period-matrix determinant is bounded using squared transverse multiplicities. This removes the analytic collision estimate from the parent. A proof route is Taylor coefficient bounds on a radius proportional to K and grouped Cauchy–Binet expansion, following the pinned collision argument; positive logarithmic weights provide the required positive transverse weights.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_FiniteTranslationData_690acb6f
open OAI.PiExponent
open OAI.PiExponent.FiniteMinorAnalysis_690acb6f
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.FiniteMinorAnalysis_690acb6f.period_matrix_collision_bound
    {m : ℕ} (K : ℕ) (w0 v theta wmin H : ℝ) (q : Fin m → ℕ)
    (hK : 0 < K) (hw0 : 0 < w0) (hv : 0 < v) (htheta : 0 < theta)
    (hmin : 0 < wmin) (hH : 0 < H)
    (hwmin : ∀ i, wmin ≤ MatrixArithmetic.logWeights q i)
    (selection : Rows K v theta q H → Columns w0 q H)
    (f : Choices K v theta q H) :
    ‖(periodMatrix selection f).det‖ ≤ Real.exp
      (-(Real.log 2 / 4) *
          (∑ a : Transverse q H,
            (OAI.PiExponent.FiniteMinorAnalysis_690acb6f.multiplicity (fun r => (f r).1) a : ℝ) ^ 2) +
        (rowCount K v theta q H : ℝ) * H *
          (holomorphicError K w0 v wmin +
            collisionRemainder (rowCount K v theta q H) H)) := by sorry
