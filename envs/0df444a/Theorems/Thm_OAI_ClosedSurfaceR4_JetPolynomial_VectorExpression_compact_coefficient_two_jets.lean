-- Prove2me | Theorems.Thm_OAI_ClosedSurfaceR4_JetPolynomial_VectorExpression_compact_coefficient_two_jets
-- name    : OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.compact_coefficient_two_jets
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T12:47:31.000252+00:00
-- url     : https://prove2.me/theorems/52524783-d9e2-4f33-8d7e-51ed12c40f90
-- title:
--   OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.compact_coefficient_two_jets: intermediate lemma from OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ClosedSurfaceR4.FiniteOrderSmoothing.smooth_isometric_immersion`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Smooth isometric immersions of closed surfaces into Euclidean four-space*, OpenAI Math Release, September 23, 2026, result family 333, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.compact_coefficient_two_jets` of [lean/OAI/Geometry/SurfaceImmersion/Geometry/CoefficientJetBounds.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/CoefficientJetBounds.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression`, with `open Set`, `open scoped ContDiff Matrix`, `open LocalPeriodicExpansion WeightedEstimates`):
--
--   ```lean
--   theorem compact_coefficient_two_jets {S : TopologicalSpace.Opens Base} {O Q : Set LowJet}
--       (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
--       (R : ℕ → VectorExpression) (L N : ℕ) (hN : 2 ≤ N)
--       (hRs : ∀ i < L, (R i).SmoothCoeffs O) (hRo : ∀ i < L, ∀ a, (R i a).order ≤ N)
--       (ℓ : Base →L[ℝ] ℝ) :
--       ∃ loss : ℕ, ∀ B : ℝ, 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
--         ∀ (G : Base → Space) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
--         ContDiff ℝ ∞ G → MapsTo (lowJet G) S Q →
--         WeightedBound S s (N+2) B (lowJet G) →
--         ∀ U : ℕ → Family S R4, (∀ i < L, Represents G (R i) (U i)) →
--         ∀ i < L, ∀ k j : Fin 3, ∀ p ∈ S,
--           ‖(coefficientFamilyDerivative (U i) k).fastValue ℓ z p‖ ≤ D/s^loss ∧
--           ‖(coefficientFamilyDerivative (coefficientFamilyDerivative (U i) k) j).fastValue ℓ z p‖ ≤
--             D/s^loss
--   ```
--
--   **Definitions.** The statement is written with `OAI.ClosedSurfaceR4.JetPolynomial.Base`, `OAI.ClosedSurfaceR4.JetPolynomial.LowIndex`, `OAI.ClosedSurfaceR4.JetPolynomial.LowJet`, `OAI.ClosedSurfaceR4.JetPolynomial.Space`, `OAI.ClosedSurfaceR4.JetPolynomial.lowJet`, `OAI.ClosedSurfaceR4.WeightedEstimates.WeightedBound` and `OAI.ClosedSurfaceR4.JetPolynomial.Expression.order` (definitions bundle `OAIQ249SI001` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.R4` (definitions bundle `OAIQ249SI002` of this split); `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family` (definitions bundle `OAIQ249SI004` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression` and `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.SmoothCoeffs` (definitions bundle `OAIQ249SI007` of this split); `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.Represents`, `OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.coefficientFamilyDerivative` and `OAI.ClosedSurfaceR4.LocalPeriodicExpansion.Family.fastValue` (definitions bundle `OAIQ249SI012` of this split).
--
--   **Used by.** The proofs of `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_longitudinal_profile`, `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_mixed_profile` and `OAI.ClosedSurfaceR4.SurfaceVelocityFamily.Loop.uniform_scaled_longitudinal_profile` of this split import it.
-- source:
--   OpenAI, Smooth isometric immersions of closed surfaces into Euclidean four-space, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 333; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Geometry/SurfaceImmersion/Geometry/CoefficientJetBounds.lean (declaration OAI.ClosedSurfaceR4.JetPolynomial.VectorExpression.compact_coefficient_two_jets)

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
open Set
open scoped ContDiff Matrix
namespace ClosedSurfaceR4.JetPolynomial.VectorExpression
open LocalPeriodicExpansion WeightedEstimates

theorem compact_coefficient_two_jets {S : TopologicalSpace.Opens Base} {O Q : Set LowJet}
    (hO : IsOpen O) (hQ : IsCompact Q) (hQO : Q ⊆ O)
    (R : ℕ → VectorExpression) (L N : ℕ) (hN : 2 ≤ N)
    (hRs : ∀ i < L, (R i).SmoothCoeffs O) (hRo : ∀ i < L, ∀ a, (R i a).order ≤ N)
    (ℓ : Base →L[ℝ] ℝ) :
    ∃ loss : ℕ, ∀ B : ℝ, 1 ≤ B → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (G : Base → Space) (s z : ℝ), 0 < z → z ≤ s → s ≤ 1 →
      ContDiff ℝ ∞ G → MapsTo (lowJet G) S Q →
      WeightedBound S s (N+2) B (lowJet G) →
      ∀ U : ℕ → Family S R4, (∀ i < L, Represents G (R i) (U i)) →
      ∀ i < L, ∀ k j : Fin 3, ∀ p ∈ S,
        ‖(coefficientFamilyDerivative (U i) k).fastValue ℓ z p‖ ≤ D/s^loss ∧
        ‖(coefficientFamilyDerivative (coefficientFamilyDerivative (U i) k) j).fastValue ℓ z p‖ ≤
          D/s^loss := by
  sorry

end ClosedSurfaceR4.JetPolynomial.VectorExpression

end

end OAI
end
