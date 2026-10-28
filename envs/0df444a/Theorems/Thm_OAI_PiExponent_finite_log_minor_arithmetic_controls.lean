-- Prove2me | Theorems.Thm_OAI_PiExponent_finite_log_minor_arithmetic_controls
-- name    : OAI.PiExponent.finite_log_minor_arithmetic_controls
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T03:57:13.762461+00:00
-- url     : https://prove2.me/theorems/84ac271b-41d6-4b2d-b407-b15d6158dfe8
-- title:
--   Finite logarithmic minors satisfy the sharp-budget arithmetic lower bound
-- statement:
--   Every nonzero selected rational logarithmic minor has normalized log norm at least minus one plus its mean transverse row weight minus the explicit arithmetic allowance with LCM constant 4 log 2. The mean lies between zero and theta. No approximation, rank, volume, or strict budget margin is assumed.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_FiniteMinorComparison
open OAI.PiExponent
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.finite_log_minor_arithmetic_controls
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
    0 ≤ OAI.PiExponent.MatrixArithmetic.meanRowWeight K v0 theta q H ∧
    OAI.PiExponent.MatrixArithmetic.meanRowWeight K v0 theta q H ≤ theta ∧
    -(1 - OAI.PiExponent.MatrixArithmetic.meanRowWeight K v0 theta q H) -
      OAI.PiExponent.FiniteMinorComparison.arithmeticError m v0 theta F wmin ≤
      Real.log ‖(OAI.PiExponent.MatrixArithmetic.selectedMinor K
        w0 v0 theta F H p q selection).det‖ /
        ((Fintype.card (OAI.PiExponent.InterpolationMatrix.Row K v0 theta
          (OAI.PiExponent.MatrixArithmetic.logWeights q) H) : ℝ) * H) := by sorry
