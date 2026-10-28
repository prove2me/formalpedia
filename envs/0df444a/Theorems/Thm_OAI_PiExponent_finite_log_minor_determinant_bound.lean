-- Prove2me | Theorems.Thm_OAI_PiExponent_finite_log_minor_determinant_bound
-- name    : OAI.PiExponent.finite_log_minor_determinant_bound
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T04:13:01.568887+00:00
-- url     : https://prove2.me/theorems/9cec50be-098f-4ebd-9c81-398ca937900a
-- title:
--   Normalized arithmetic lower bound for a nonzero selected minor
-- statement:
--   A nonzero selected logarithmic minor has the target's normalized logarithmic lower bound, with the explicit arithmetic allowance.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_FiniteMinorComparison
open OAI.PiExponent
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.finite_log_minor_determinant_bound
    (m K : ℕ) (w0 v0 theta F wmin H : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0)
    (htheta : 0 < theta) (hF : 0 ≤ F) (hmin : 0 < wmin)
    (hH : 0 < H) (hq : ∀ i, 2 ≤ q i)
    (hwmin : ∀ i, wmin ≤ OAI.PiExponent.MatrixArithmetic.logWeights q i)
    (selection :
      OAI.PiExponent.InterpolationMatrix.Row K v0 theta
        (OAI.PiExponent.MatrixArithmetic.logWeights q) H →
      OAI.PiExponent.InterpolationMatrix.Column w0
        (OAI.PiExponent.MatrixArithmetic.logWeights q) H)
    (hdet : (OAI.PiExponent.MatrixArithmetic.selectedMinor K
      w0 v0 theta F H p q selection).det ≠ 0) :
    -(1 - OAI.PiExponent.MatrixArithmetic.meanRowWeight K v0 theta q H) -
      OAI.PiExponent.FiniteMinorComparison.arithmeticError m v0 theta F wmin ≤
      Real.log ‖(OAI.PiExponent.MatrixArithmetic.selectedMinor K
        w0 v0 theta F H p q selection).det‖ /
        ((Fintype.card (OAI.PiExponent.InterpolationMatrix.Row K v0 theta
          (OAI.PiExponent.MatrixArithmetic.logWeights q) H) : ℝ) * H) := by sorry
