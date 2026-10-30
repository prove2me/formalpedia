-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_angular_balanced_smooth_product_neighborhood
-- name    : OAI.CubicFirstMoment.angular_balanced_smooth_product_neighborhood
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:14:09.160999+00:00
-- url     : https://prove2.me/theorems/5380c594-bab6-45a6-a8a6-77e7a39d4f88
-- title:
--   OAI.CubicFirstMoment.angular_balanced_smooth_product_neighborhood: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.angular_balanced_smooth_product_neighborhood` of [lean/OAI/NumberTheory/CubicMoment/Angular/AngularBalancedSmoothNeighborhood.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularBalancedSmoothNeighborhood.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Filter Set`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem angular_balanced_smooth_product_neighborhood (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
--       (hHuxley : HuxleyAdditiveLargeSieve)
--       (W : ι → ℝ → ℂ) (hW : ∀ i, HasCompactSupport (W i))
--       (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0) (hsm : ∀ i, ContDiff ℝ ∞ (W i))
--       (hWlow : ∀ i x, x < 1 → W i x = 0) (hWup : ∀ i x, 2 < x → W i x = 0)
--       (hWnorm : ∀ i x, ‖W i x‖ ≤ 1)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
--       (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
--       {D : ℝ} (hD : 0 < D) :
--       ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y : ℝ) (X : ι → ℝ)
--         (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
--         (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)),
--         Y₀ ≤ Y → F ≤ D*Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
--         Y/D ≤ ∏ i, X i → (∏ i, X i) ≤ D*Y →
--         (∀ i, q i ≠ 0) → (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
--         (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(37/100:ℝ)) →
--         (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
--           norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
--         (∑ a ∈ P, ‖∏ i, primaryAngularShortSmoothSum ℓ (A i) a.1 a.2 (q i) (η i) (W i) (X i/2) (t i)‖^2) ≤
--           Y^(7/3-ε)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` and `OAI.CubicFirstMoment.EisensteinArithmeticFunction` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.GammaInverseFiniteOrder` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.AngularUnitCompatible` and `OAI.CubicFirstMoment.ShortArithmeticFactor` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve`, `OAI.CubicFirstMoment.PrimarySquarefreePair` and `OAI.CubicFirstMoment.PrimitiveAngularHeckeInput` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.primaryAngularShortSmoothSum` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.Residues`, `OAI.CubicFirstMoment.modulus` and `OAI.CubicFirstMoment.norm` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.angular_balanced_common_squarefree_exponents` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularBalancedSmoothNeighborhood.lean (declaration OAI.CubicFirstMoment.angular_balanced_smooth_product_neighborhood)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A015

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_balanced_smooth_product_neighborhood (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    (hHuxley : HuxleyAdditiveLargeSieve)
    (W : ι → ℝ → ℂ) (hW : ∀ i, HasCompactSupport (W i))
    (hpos : ∀ i, tsupport (W i) ⊆ Ioi 0) (hsm : ∀ i, ContDiff ℝ ∞ (W i))
    (hWlow : ∀ i x, x < 1 → W i x = 0) (hWup : ∀ i x, 2 < x → W i x = 0)
    (hWnorm : ∀ i x, ‖W i x‖ ≤ 1)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ)))
    {D : ℝ} (hD : 0 < D) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset (Eisenstein × Eisenstein)),
      Y₀ ≤ Y → F ≤ D*Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      Y/D ≤ ∏ i, X i → (∏ i, X i) ≤ D*Y →
      (∀ i, q i ≠ 0) → (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(37/100:ℝ)) →
      (∀ a ∈ P, PrimarySquarefreePair a ∧ norm a.1 ≤ Y^(1/3+κ) ∧
        norm a.2 ≤ Y^(1/3+κ) ∧ Y^(1/1000:ℝ) ≤ norm a.1) →
      (∑ a ∈ P, ‖∏ i, primaryAngularShortSmoothSum ℓ (A i) a.1 a.2 (q i) (η i) (W i) (X i/2) (t i)‖^2) ≤
        Y^(7/3-ε) := by
  sorry

end CubicFirstMoment

end

end OAI
end
