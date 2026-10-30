-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_uniform_core_block_polynomial_height
-- name    : OAI.CubicFirstMoment.uniform_core_block_polynomial_height
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T04:30:01.898444+00:00
-- url     : https://prove2.me/theorems/3c832136-ab60-44cc-8826-766600128cdd
-- title:
--   OAI.CubicFirstMoment.uniform_core_block_polynomial_height: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.uniform_core_block_polynomial_height` of [lean/OAI/NumberTheory/CubicMoment/Estimates/PolynomialHeightCoreBlock.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/PolynomialHeightCoreBlock.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open scoped BigOperators`, `open Filter`):
--
--   ```lean
--   theorem uniform_core_block_polynomial_height (hpub : PrimitiveResidueHeckeInput)
--       (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
--       {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
--       (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (k : ℕ) :
--       ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
--       ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
--         LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
--         (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
--       ∃ (C T₀ : ℝ) (A : ℕ), 0 < C ∧
--       ∀ (r : γ) (X : ι → ℝ) (B : ℝ) (i j : ℕ) (e : Eisenstein) (u : ℝ)
--         (H : Finset Eisenstein), T₀ ≤ L r →
--         (∏ a, X a) = L r → (∀ a, (2*L r)^c < X a) →
--         0 ≤ B → B ≤ (L r)^(1+η) → coreDyadicConductor i j ≤ B →
--         (1+Real.log (L r))^A ≤ 8*coreDyadicConductor i j →
--         e ≠ 0 → norm e ≤ (L r)^σ → 1+|u| ≤ (L r)^(9/25:ℝ) →
--         H ⊆ coreDyadicBlock B i j →
--         (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 1 e u (W r) X‖^2) ≤
--           C*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.GammaInverseFiniteOrder`, `OAI.CubicFirstMoment.GammaQuotientStripBound` and `OAI.CubicFirstMoment.LogarithmicWeightFamily` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.coreDyadicConductor` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.CubicSupplementaryPeriodicity` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.HuxleyAdditiveLargeSieve` and `OAI.CubicFirstMoment.PrimitiveResidueHeckeInput` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.coreDyadicBlock` (definitions bundle `OAIQ096A008` of this split); `OAI.CubicFirstMoment.fullStructuredPrimeSum` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.Eisenstein` and `OAI.CubicFirstMoment.norm` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.coprime_noncube_mellin_integral_saving`, `OAI_CubicFirstMoment_height_all_frequency_cutoff_mass`, `OAI.CubicFirstMoment.height_radial_form_saving` and `OAI_CubicFirstMoment_noncube_signed_mellin_integral_saving` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/PolynomialHeightCoreBlock.lean (declaration OAI.CubicFirstMoment.uniform_core_block_polynomial_height)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A015

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators
open Filter
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

theorem uniform_core_block_polynomial_height (hpub : PrimitiveResidueHeckeInput)
    (hHuxley : HuxleyAdditiveLargeSieve) (hperiod : CubicSupplementaryPeriodicity)
    {c R : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1) (hR : 1 ≤ R)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) (k : ℕ) :
    ∃ η σ : ℝ, 0 < η ∧ η ≤ 1 ∧ 0 < σ ∧
    ∀ (L : γ → ℝ) (W : γ → ι → ℝ → ℂ), (∀ r, 1 ≤ L r) →
      LogarithmicWeightFamily (fun z : γ × ι => L z.1) (fun z => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → (∀ r i x, R < x → W r i x = 0) →
    ∃ (C T₀ : ℝ) (A : ℕ), 0 < C ∧
    ∀ (r : γ) (X : ι → ℝ) (B : ℝ) (i j : ℕ) (e : Eisenstein) (u : ℝ)
      (H : Finset Eisenstein), T₀ ≤ L r →
      (∏ a, X a) = L r → (∀ a, (2*L r)^c < X a) →
      0 ≤ B → B ≤ (L r)^(1+η) → coreDyadicConductor i j ≤ B →
      (1+Real.log (L r))^A ≤ 8*coreDyadicConductor i j →
      e ≠ 0 → norm e ≤ (L r)^σ → 1+|u| ≤ (L r)^(9/25:ℝ) →
      H ⊆ coreDyadicBlock B i j →
      (∑ h ∈ H, ‖fullStructuredPrimeSum R h 1 1 e u (W r) X‖^2) ≤
        C*(L r)^2*B^(1/3:ℝ)/(1+Real.log (L r))^k := by
  sorry

end CubicFirstMoment

end

end OAI
end
