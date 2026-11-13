-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_exists_bounded_coefficients
-- name    : OAI.ClosedSurfaceR4.JetPolynomial.exists_bounded_coefficients
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:47:37.849022+00:00
-- url     : https://prove2.me/theorems/a2481e99-713e-48e9-9217-559a50d56081
-- title:
--   OAI.ClosedSurfaceR4.JetPolynomial.exists_bounded_coefficients: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.JetPolynomial.exists_bounded_coefficients` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/BoundedCoefficientRecursion.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/BoundedCoefficientRecursion.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.JetPolynomial`, with `open scoped ContDiff`, `open LocalPeriodicExpansion CovarianceCorrector WeightedEstimates`):
--
--   ```lean
--   theorem exists_bounded_coefficients {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
--       (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
--       (dx dy : Fin 2) (n : ℕ) (ℓ : Base →L[ℝ] ℝ)
--       {Y C X₀ : LowJet → R4} {V : LowJet → C(Period, R4)} {q : LowJet → ℝ}
--       (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
--       (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
--       (hdet : ∀ Q ∈ O, PeriodicCorrector.gramDet (Y Q) (C Q) ≠ 0)
--       (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
--       (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q) :
--       ∃ d : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
--         ∀ (G : Base → Space) (g : Geometry (E := R4) S (coordinateVector dy)),
--         ContDiff ℝ ∞ G → Set.MapsTo (lowJet G) S K →
--         (∀ p ∈ S, g.Y p = Y (lowJet G p)) →
--         (∀ p ∈ S, g.C p = C (lowJet G p)) →
--         (∀ p ∈ S, g.X₀ p = X₀ (lowJet G p)) →
--         (∀ p ∈ S, g.V.val p = V (lowJet G p)) →
--         (∀ p ∈ S, g.q p = q (lowJet G p)) →
--         ∃ U : ℕ → Family S R4,
--           U 0 = g.initial ∧ (∀ i p, p ∈ S → average ((U i).val p) = 0) ∧
--           (g.yyCoefficient U 1).fluct = 0 ∧
--           (∀ Z : Set Base, IsOpen Z → Z ⊆ S → (∀ p ∈ Z, g.initial.val p = 0) →
--             ∀ i p, p ∈ Z → (U i).val p = 0) ∧
--           (∀ r, 1 ≤ r → r ≤ n →
--             (g.xxCoefficient (coordinateVector dx) U r).fluct = 0 ∧
--             (g.xyCoefficient (coordinateVector dx) U r).fluct = 0 ∧
--             (g.yyCoefficient U (r + 1)).fluct = 0) ∧
--           (∀ i, VectorExpression.Represents G
--             (MetricPolynomial.coefficients Y C X₀ V q dx dy n i) (U i)) ∧
--           ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
--             WeightedBound S s (m + (2 * n + 2)) B (lowJet G) → ∀ F : Base → R4,
--             WeightedBound S z m (D * z / s ^ d)
--               (fun p => finiteAnsatz F U ℓ (n + 1) z p - F p)
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.CovarianceCorrector.Period`, `OAI.ClosedSurfaceR4.CovarianceCorrector.average`, `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.LowIndex`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.coordinateVector`, `OAI.ClosedSurfaceR4.JetPolynomial.lowJet` and `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.R4` and `OAI.ClosedSurfaceR4.PeriodicCorrector.gramDet` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.instAddCommGroupFamily` and `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.val` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry` and `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.fluct` (definitions bundle `OAIQ249SI010` of this split); `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.finiteAnsatz`, `OAI.ClosedSurfaceR4.JetPolynomial.MetricPolynomial.coefficients`, `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.Represents`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.initial`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xxCoefficient`, `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.xyCoefficient` and `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Geometry.yyCoefficient` (definitions bundle `OAIQ249SI012` of this split).
--
--   **Used by.** The proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.SmoothingAtlas.supported_phase_primitive_metric` of this split imports it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/BoundedCoefficientRecursion.lean (declaration OAI.ClosedSurfaceR4.JetPolynomial.exists_bounded_coefficients)

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
open LocalPeriodicExpansion CovarianceCorrector WeightedEstimates

theorem exists_bounded_coefficients {S : TopologicalSpace.Opens Base} {O K : Set LowJet}
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (dx dy : Fin 2) (n : ℕ) (ℓ : Base →L[ℝ] ℝ)
    {Y C X₀ : LowJet → R4} {V : LowJet → C(Period, R4)} {q : LowJet → ℝ}
    (hY : ContDiffOn ℝ ∞ Y O) (hC : ContDiffOn ℝ ∞ C O) (hX : ContDiffOn ℝ ∞ X₀ O)
    (hV : ContDiffOn ℝ ∞ (fun z : LowJet × ℝ => V z.1 (z.2 : Period)) (O ×ˢ Set.univ))
    (hdet : ∀ Q ∈ O, PeriodicCorrector.gramDet (Y Q) (C Q) ≠ 0)
    (hq : ContDiffOn ℝ ∞ q O) (hqp : ∀ Q ∈ O, 0 < q Q)
    (hcircle : ∀ Q ∈ O, ∀ t, inner ℝ (V Q t) (V Q t) = q Q) :
    ∃ d : ℕ, ∀ (m : ℕ) (B : ℝ), 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : Base → Space) (g : Geometry (E := R4) S (coordinateVector dy)),
      ContDiff ℝ ∞ G → Set.MapsTo (lowJet G) S K →
      (∀ p ∈ S, g.Y p = Y (lowJet G p)) →
      (∀ p ∈ S, g.C p = C (lowJet G p)) →
      (∀ p ∈ S, g.X₀ p = X₀ (lowJet G p)) →
      (∀ p ∈ S, g.V.val p = V (lowJet G p)) →
      (∀ p ∈ S, g.q p = q (lowJet G p)) →
      ∃ U : ℕ → Family S R4,
        U 0 = g.initial ∧ (∀ i p, p ∈ S → average ((U i).val p) = 0) ∧
        (g.yyCoefficient U 1).fluct = 0 ∧
        (∀ Z : Set Base, IsOpen Z → Z ⊆ S → (∀ p ∈ Z, g.initial.val p = 0) →
          ∀ i p, p ∈ Z → (U i).val p = 0) ∧
        (∀ r, 1 ≤ r → r ≤ n →
          (g.xxCoefficient (coordinateVector dx) U r).fluct = 0 ∧
          (g.xyCoefficient (coordinateVector dx) U r).fluct = 0 ∧
          (g.yyCoefficient U (r + 1)).fluct = 0) ∧
        (∀ i, VectorExpression.Represents G
          (MetricPolynomial.coefficients Y C X₀ V q dx dy n i) (U i)) ∧
        ∀ (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
          WeightedBound S s (m + (2 * n + 2)) B (lowJet G) → ∀ F : Base → R4,
          WeightedBound S z m (D * z / s ^ d)
            (fun p => finiteAnsatz F U ℓ (n + 1) z p - F p) := by
  sorry

end ClosedSurfaceR4.JetPolynomial

end

end OAI
end
