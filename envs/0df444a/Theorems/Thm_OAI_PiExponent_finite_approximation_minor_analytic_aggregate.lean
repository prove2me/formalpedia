-- Prove2me | Theorems.Thm_OAI_PiExponent_finite_approximation_minor_analytic_aggregate
-- name    : OAI.PiExponent.finite_approximation_minor_analytic_aggregate
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T03:57:53.993567+00:00
-- url     : https://prove2.me/theorems/690acb6f-9bb5-4bbd-9d0c-a47fa06b1c01
-- title:
--   Finite approximations yield a selection-uniform analytic minor estimate
-- statement:
--   Finite simultaneous approximations to pi give an eventual, selection-uniform normalized logarithmic upper bound for the actual truncated rational-center minors. It retains the mean row weight and the height-dependent collision rate, and has a selection-independent remainder tending to zero. It assumes neither rank nor the target's error/collision gaps or special infinite admissible-family identities.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_FiniteMinorComparison
open OAI.PiExponent
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.finite_approximation_minor_analytic_aggregate
    (m K : ℕ) (w0 v0 theta : ℚ) (nu A eta F wmin : ℝ)
    (p : Fin m → ℤ) (q : Fin m → ℕ)
    (hm : 0 < m) (hK : 0 < K)
    (hw0 : 0 < w0) (hv0 : 0 < v0)
    (htheta : 0 < theta) (htheta1 : theta < 1)
    (hnu : 0 ≤ nu) (hA : 0 < A) (hA1 : A < 1)
    (heta : 0 < eta) (heta1 : eta < 1)
    (hF : 0 < F) (hFlarge : 2 / (theta : ℝ) < F)
    (hmin : 0 < wmin) (hq : ∀ i, 2 ≤ q i)
    (hwmin : ∀ i, wmin ≤ OAI.PiExponent.MatrixArithmetic.logWeights q i)
    (happrox : ∀ i,
      |Real.pi - (p i : ℝ) / (q i : ℝ)| ≤ (q i : ℝ) ^ (-nu)) :
    ∃ error : ℝ → ℝ, Tendsto error atTop (𝓝 0) ∧
      ∀ᶠ H : ℝ in atTop, ∀ selection :
        OAI.PiExponent.InterpolationMatrix.Row K (v0 : ℝ) (theta : ℝ)
          (OAI.PiExponent.MatrixArithmetic.logWeights q) H →
        OAI.PiExponent.InterpolationMatrix.Column (w0 : ℝ)
          (OAI.PiExponent.MatrixArithmetic.logWeights q) H,
        (OAI.PiExponent.MatrixArithmetic.selectedMinor K
          (w0 : ℝ) (v0 : ℝ) (theta : ℝ) F H p q selection).det ≠ 0 →
        Real.log ‖(OAI.PiExponent.MatrixArithmetic.selectedMinor K
          (w0 : ℝ) (v0 : ℝ) (theta : ℝ) F H p q selection).det‖ /
          ((Fintype.card (OAI.PiExponent.InterpolationMatrix.Row K
            (v0 : ℝ) (theta : ℝ)
            (OAI.PiExponent.MatrixArithmetic.logWeights q) H) : ℝ) * H) ≤
        OAI.PiExponent.FiniteMinorComparison.analyticError K
          nu F (v0 : ℝ) (w0 : ℝ) wmin + error H +
        max (-OAI.PiExponent.FiniteMinorComparison.collisionRate
          K (v0 : ℝ) (theta : ℝ) A eta q H)
          (-nu * (A * (1 - eta) -
            OAI.PiExponent.MatrixArithmetic.meanRowWeight K
              (v0 : ℝ) (theta : ℝ) q H)) := by sorry
