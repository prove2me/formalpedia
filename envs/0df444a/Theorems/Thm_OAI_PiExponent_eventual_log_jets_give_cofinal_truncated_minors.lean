-- Prove2me | Theorems.Thm_OAI_PiExponent_eventual_log_jets_give_cofinal_truncated_minors
-- name    : OAI.PiExponent.eventual_log_jets_give_cofinal_truncated_minors
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-24T03:56:57.628176+00:00
-- url     : https://prove2.me/theorems/f4d3ca3f-6a61-414d-893c-270bd2ac4741
-- title:
--   Filtered logarithm truncation preserves cofinal nonzero interpolation minors
-- statement:
--   A center-specific eventual logarithmic jet surjectivity hypothesis yields nonzero full-row minors at arbitrarily large positive integer heights after replacing the height-dependent logarithm by coordinate cutoffs ceil(F ceil(log q_i)/v0). This is a filtered coordinate-change and finite-dimensional linear-algebra lemma; it uses no approximation to pi.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PiExponent.lean

import Definitions.Def_PiExponent_FiniteMinorComparison
open OAI.PiExponent
open Filter Topology
open scoped BigOperators

theorem OAI.PiExponent.eventual_log_jets_give_cofinal_truncated_minors
    (m K : ℕ) (w0 v0 theta : ℚ) (F : ℝ)
    (p : Fin m → ℤ) (q w : Fin m → ℕ)
    (hK : 0 < K) (hw0 : 0 < w0) (hv0 : 0 < v0)
    (htheta : 0 < theta) (hF : 0 < F)
    (hFlarge : 2 / (theta : ℝ) < F)
    (hq : ∀ i, 2 ≤ q i)
    (hw : ∀ i, w i = Nat.ceil (Real.log (q i : ℝ)))
    (hjet : OAI.PiExponent.eventualLogJetSurjective m K w0 v0 theta w
      (fun j i => (j.val : ℂ) *
        OAI.PiExponent.MatrixArithmetic.rationalCenters p q i)) :
    ∀ L : ℝ, ∃ H : ℕ, L ≤ (H : ℝ) ∧ 0 < H ∧
      ∃ selection :
        OAI.PiExponent.InterpolationMatrix.Row K (v0 : ℝ) (theta : ℝ)
          (OAI.PiExponent.MatrixArithmetic.logWeights q) (H : ℝ) →
        OAI.PiExponent.InterpolationMatrix.Column (w0 : ℝ)
          (OAI.PiExponent.MatrixArithmetic.logWeights q) (H : ℝ),
        (OAI.PiExponent.MatrixArithmetic.selectedMinor K
          (w0 : ℝ) (v0 : ℝ) (theta : ℝ) F (H : ℝ) p q selection).det ≠ 0 := by sorry
