-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_MetricPolynomial_compact_metric_error
-- name    : OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.compact_metric_error
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:45:48.942207+00:00
-- url     : https://prove2.me/theorems/51bcde4c-92e8-41e5-82a8-d0d0ecd13398
-- title:
--   OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.compact_metric_error: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.compact_metric_error` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/QuantitativeMetricExpansion.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/QuantitativeMetricExpansion.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial`, with `open scoped ContDiff`, `open LocalPeriodicExpansion WeightedEstimates CovarianceCorrector`):
--
--   ```lean
--   theorem compact_metric_error {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
--       (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
--       (X Y : VectorExpression) (R : ℕ → VectorExpression)
--       (hXs : X.SmoothCoeffs O) (hYs : Y.SmoothCoeffs O) (hRs : ∀ i, (R i).SmoothCoeffs O)
--       (n : ℕ) (hX : ∀ a, (X a).order ≤ 2) (hY : ∀ a, (Y a).order ≤ 2)
--       (hR : ∀ j < n + 1, ∀ a, (R j a).order ≤ 2 * j + 2)
--       (dx dy : Fin 2) (b c : Bool) (ℓ : Base →L[ℝ] ℝ)
--       (hℓx : ℓ (coordinateVector dx) = 1) (hℓy : ℓ (coordinateVector dy) = 0) :
--       ∃ d : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
--         ∀ (G : Base → Space) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
--         ContDiff ℝ ∞ G → Set.MapsTo (lowJet G) S K →
--         WeightedBound S s (m + (2 * (n + 1) + 1)) B (lowJet G) →
--         ∀ (g : Geometry (E := R4) S (coordinateVector dy)) (U : ℕ → Family S R4)
--           (F : Base → R4),
--           VectorExpression.Represents G X g.longitudinal →
--           VectorExpression.Represents G Y g.transverse →
--           (∀ i, VectorExpression.Represents G (R i) (U i)) →
--           U 0 = g.initial → (g.yyCoefficient U 1).fluct = 0 →
--           (∀ r, 1 ≤ r → r ≤ n →
--             (g.xxCoefficient (coordinateVector dx) U r).fluct = 0 ∧
--             (g.xyCoefficient (coordinateVector dx) U r).fluct = 0 ∧
--             (g.yyCoefficient U (r + 1)).fluct = 0) →
--           ContDiffOn ℝ ∞ F S →
--           (∀ p ∈ S, fderiv ℝ F p (coordinateVector dx) = g.X₀ p + average (g.V.val p)) →
--           (∀ p ∈ S, fderiv ℝ F p (coordinateVector dy) = g.Y p) →
--           WeightedBound S z m (D * z ^ (n + 1) / s ^ d)
--             (fun p => inner ℝ
--               (fderiv ℝ (finiteAnsatz F U ℓ (n + 1) z) p
--                 (metricDirection (coordinateVector dx) (coordinateVector dy) b))
--               (fderiv ℝ (finiteAnsatz F U ℓ (n + 1) z) p
--                 (metricDirection (coordinateVector dx) (coordinateVector dy) c)) -
--               meanMetric g (coordinateVector dx) U n b c z p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.CovarianceCorrector.Period`, `OAI.ClosedSurfaceR4.CovarianceCorrector.average`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.LowIndex`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.coordinateVector`, `OAI.ClosedSurfaceR4.JetPolynomial.lowJet`, `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` and `OAI.ClosedSurfaceR4.JetPolynomial.Expression.order` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.R4` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.instAddCommGroupFamily` and `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.val` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.metricDirection` (definitions bundle `OAIQ249SI005` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression` and `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.SmoothCoeffs` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.fluct`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.longitudinal` and `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.transverse` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.finiteAnsatz`, `OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.meanMetric`, `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.Represents`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.initial`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xxCoefficient`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xyCoefficient` and `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.yyCoefficient` (definitions bundle `OAIQ249SI012` of this split).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_primitive_metric_remainder` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/QuantitativeMetricExpansion.lean (declaration OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.compact_metric_error)

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

namespace ClosedSurfaceR4.JetPolynomial
open LocalPeriodicExpansion WeightedEstimates CovarianceCorrector

namespace MetricPolynomial

theorem compact_metric_error {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (X Y : VectorExpression) (R : ℕ → VectorExpression)
    (hXs : X.SmoothCoeffs O) (hYs : Y.SmoothCoeffs O) (hRs : ∀ i, (R i).SmoothCoeffs O)
    (n : ℕ) (hX : ∀ a, (X a).order ≤ 2) (hY : ∀ a, (Y a).order ≤ 2)
    (hR : ∀ j < n + 1, ∀ a, (R j a).order ≤ 2 * j + 2)
    (dx dy : Fin 2) (b c : Bool) (ℓ : Base →L[ℝ] ℝ)
    (hℓx : ℓ (coordinateVector dx) = 1) (hℓy : ℓ (coordinateVector dy) = 0) :
    ∃ d : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : Base → Space) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      ContDiff ℝ ∞ G → Set.MapsTo (lowJet G) S K →
      WeightedBound S s (m + (2 * (n + 1) + 1)) B (lowJet G) →
      ∀ (g : Geometry (E := R4) S (coordinateVector dy)) (U : ℕ → Family S R4)
        (F : Base → R4),
        VectorExpression.Represents G X g.longitudinal →
        VectorExpression.Represents G Y g.transverse →
        (∀ i, VectorExpression.Represents G (R i) (U i)) →
        U 0 = g.initial → (g.yyCoefficient U 1).fluct = 0 →
        (∀ r, 1 ≤ r → r ≤ n →
          (g.xxCoefficient (coordinateVector dx) U r).fluct = 0 ∧
          (g.xyCoefficient (coordinateVector dx) U r).fluct = 0 ∧
          (g.yyCoefficient U (r + 1)).fluct = 0) →
        ContDiffOn ℝ ∞ F S →
        (∀ p ∈ S, fderiv ℝ F p (coordinateVector dx) = g.X₀ p + average (g.V.val p)) →
        (∀ p ∈ S, fderiv ℝ F p (coordinateVector dy) = g.Y p) →
        WeightedBound S z m (D * z ^ (n + 1) / s ^ d)
          (fun p => inner ℝ
            (fderiv ℝ (finiteAnsatz F U ℓ (n + 1) z) p
              (metricDirection (coordinateVector dx) (coordinateVector dy) b))
            (fderiv ℝ (finiteAnsatz F U ℓ (n + 1) z) p
              (metricDirection (coordinateVector dx) (coordinateVector dy) c)) -
            meanMetric g (coordinateVector dx) U n b c z p) := by
  sorry

end MetricPolynomial
end ClosedSurfaceR4.JetPolynomial

end

end OAI
end
