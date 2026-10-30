-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_dominant_balanced_full_factor_neighborhood
-- name    : OAI.CubicFirstMoment.dominant_balanced_full_factor_neighborhood
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:59:04.94647+00:00
-- url     : https://prove2.me/theorems/043395be-1d4a-40f2-9ffc-4a5f6253f6e1
-- title:
--   OAI.CubicFirstMoment.dominant_balanced_full_factor_neighborhood: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.dominant_balanced_full_factor_neighborhood` of [lean/OAI/NumberTheory/CubicMoment/Estimates/DominantNeighborhood.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/DominantNeighborhood.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Set`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem dominant_balanced_full_factor_neighborhood (hpub : PrimitiveResidueHeckeInput)
--       (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
--       (hsm : ContDiff ℝ ∞ W) (hWlow : ∀ x : ℝ, x < 1 → W x = 0)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
--       (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (D : ℝ) :
--       ∃ K Y₀ : ℝ, 0 ≤ K ∧ 2 ≤ Y₀ ∧
--         ∀ (P : Finset (Eisenstein × Eisenstein)) (q : Eisenstein) (η : MulChar (Residues q) ℂ)
--           (A : EisensteinArithmeticFunction) (F Y X t : ℝ), Y₀ ≤ Y →
--         ShortArithmeticFactor F A → F ≤ D*Y → q ≠ 0 →
--         (∀ e : Eisensteinˣ, η (Ideal.Quotient.mk (modulus q) e) = 1) →
--         norm q ≤ Y^(1/100000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
--         Y^(9999/10000:ℝ) ≤ X → X ≤ D*Y → (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(17/50:ℝ) ∧
--           norm a.2 ≤ Y^(17/50:ℝ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
--         (∑ a ∈ P, ‖primaryShortSmoothSum A a.1 a.2 q η W (X/2) t‖^2) ≤ K*Y^(111/50:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.EisensteinArithmeticFunction` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.GammaInverseFiniteOrder` and `OAI.CubicFirstMoment.GammaQuotientStripBound` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.ShortArithmeticFactor` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.PrimarySquarefreePair` and `OAI.CubicFirstMoment.PrimitiveResidueHeckeInput` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.primaryShortSmoothSum` (definitions bundle `OAIQ096A010` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.Residues`, `OAI.CubicFirstMoment.modulus` and `OAI.CubicFirstMoment.norm` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.balanced_common_normalized_exponents` and `OAI_CubicFirstMoment_balanced_truncated_neighborhood_moment` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/DominantNeighborhood.lean (declaration OAI.CubicFirstMoment.dominant_balanced_full_factor_neighborhood)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A007
import Definitions.Def_OAIQ096A010

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped BigOperators ContDiff
namespace CubicFirstMoment

theorem dominant_balanced_full_factor_neighborhood (hpub : PrimitiveResidueHeckeInput)
    (W : ℝ → ℂ) (hW : HasCompactSupport W) (hpos : tsupport W ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ W) (hWlow : ∀ x : ℝ, x < 1 → W x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (D : ℝ) :
    ∃ K Y₀ : ℝ, 0 ≤ K ∧ 2 ≤ Y₀ ∧
      ∀ (P : Finset (Eisenstein × Eisenstein)) (q : Eisenstein) (η : MulChar (Residues q) ℂ)
        (A : EisensteinArithmeticFunction) (F Y X t : ℝ), Y₀ ≤ Y →
      ShortArithmeticFactor F A → F ≤ D*Y → q ≠ 0 →
      (∀ e : Eisensteinˣ, η (Ideal.Quotient.mk (modulus q) e) = 1) →
      norm q ≤ Y^(1/100000:ℝ) → |t| ≤ Y^(37/100:ℝ) →
      Y^(9999/10000:ℝ) ≤ X → X ≤ D*Y → (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(17/50:ℝ) ∧
        norm a.2 ≤ Y^(17/50:ℝ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖primaryShortSmoothSum A a.1 a.2 q η W (X/2) t‖^2) ≤ K*Y^(111/50:ℝ) := by
  sorry

end CubicFirstMoment

end

end OAI
end
