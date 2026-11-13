-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_MetricPolynomial_coefficients_smooth
-- name    : OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.coefficients_smooth
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:44:59.028185+00:00
-- url     : https://prove2.me/theorems/bc143942-1677-494c-ba5d-80a594410f40
-- title:
--   OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.coefficients_smooth: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.coefficients_smooth` of [lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialJetSmoothness.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialJetSmoothness.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial`, with `open scoped ContDiff`, `open CovarianceCorrector`):
--
--   ```lean
--   theorem coefficients_smooth {O : Set LowJet} (hO : IsOpen O)
--       {Y C X₀ : LowJet → R4} {V : LowJet → C(Period, R4)} {q : LowJet → ℝ}
--       (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
--       (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
--       (hd : ∀ Q ∈ O, PeriodicCorrector.gramDet (Y Q) (C Q) ≠ 0)
--       (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
--       (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q)
--       (dx dy : Fin 2) (n i : ℕ) :
--       (coefficients Y C X₀ V q dx dy n i).SmoothCoeffs O
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.CovarianceCorrector.Period`, `OAI.ClosedSurfaceR4.JetPolynomial.LowIndex` and `OAI.ClosedSurfaceR4.JetPolynomial.LowJet` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.R4` and `OAI.ClosedSurfaceR4.PeriodicCorrector.gramDet` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.SmoothCoeffs` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.coefficients` (definitions bundle `OAIQ249SI012` of this split).
--
--   **Used by.** The proofs of `OAI.ClosedSurfaceR4.JetPolynomial.exists_bounded_coefficients`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanMetric_eq_meanOperator`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.meanTensorPolynomial_global_extension`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_longitudinal_profile`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_mixed_profile`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_primitive_metric_remainder`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_scaled_longitudinal_profile` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_transverse_profiles` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Correction/PolynomialJetSmoothness.lean (declaration OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.coefficients_smooth)

import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Definitions.Def_OAIQ249SI012

section

attribute [-instance] _root_.instMembershipProdContinuousLinearMapRealIdRelLoc _root_.instVAddIntReal_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped ContDiff

namespace ClosedSurfaceR4.JetPolynomial.MetricPolynomial
open CovarianceCorrector

theorem coefficients_smooth {O : Set LowJet} (hO : IsOpen O)
    {Y C X₀ : LowJet → R4} {V : LowJet → C(Period, R4)} {q : LowJet → ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hd : ∀ Q ∈ O, PeriodicCorrector.gramDet (Y Q) (C Q) ≠ 0)
    (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q)
    (dx dy : Fin 2) (n i : ℕ) :
    (coefficients Y C X₀ V q dx dy n i).SmoothCoeffs O := by
  sorry

end ClosedSurfaceR4.JetPolynomial.MetricPolynomial

end

end OAI
end
