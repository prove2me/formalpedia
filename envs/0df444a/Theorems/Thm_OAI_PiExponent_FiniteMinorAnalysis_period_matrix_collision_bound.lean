-- Prove2me | Theorems.Thm_OAI_PiExponent_FiniteMinorAnalysis_period_matrix_collision_bound
-- name    : OAI.PiExponent.FiniteMinorAnalysis.period_matrix_collision_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T09:19:57.568059+00:00
-- url     : https://prove2.me/theorems/2f66c96e-49c4-4d53-94e8-79b232bb61ce
-- title:
--   Period minors lose an exponential factor for repeated transverse indices
-- statement:
--   The formal full-logarithm period matrix has a determinant bound depending on the sum of squared transverse multiplicities. This isolates the complex-analytic collision estimate from rational approximation, scalar translation, and the final occupancy dichotomy.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_FiniteTranslationData
open OAI.PiExponent
open OAI.PiExponent.FiniteMinorAnalysis
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.FiniteMinorAnalysis.period_matrix_collision_bound
    {m : ℕ} (K : ℕ) (w0 v theta wmin H : ℝ) (q : Fin m → ℕ)
    (hK : 0 < K) (hw0 : 0 < w0) (hv : 0 < v) (htheta : 0 < theta)
    (hmin : 0 < wmin) (hH : 0 < H)
    (hwmin : ∀ i, wmin ≤ MatrixArithmetic.logWeights q i)
    (selection : Rows K v theta q H → Columns w0 q H)
    (f : Choices K v theta q H) :
    ‖(periodMatrix selection f).det‖ ≤ Real.exp
      (-(Real.log 2 / 4) *
          (∑ a : Transverse q H, (multiplicity (fun r => (f r).1) a : ℝ) ^ 2) +
        (rowCount K v theta q H : ℝ) * H *
          (holomorphicError K w0 v wmin +
            collisionRemainder (rowCount K v theta q H) H)) := by sorry
