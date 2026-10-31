-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_first_common_prime_exponents
-- name    : OAI.CubicFirstMoment.first_common_prime_exponents
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T03:59:27.337958+00:00
-- url     : https://prove2.me/theorems/52a5c32e-cf7a-4d63-8501-fc9b614846e0
-- title:
--   OAI.CubicFirstMoment.first_common_prime_exponents: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.first_common_prime_exponents` of [lean/OAI/NumberTheory/CubicMoment/Estimates/CommonPrimeIndicatorExponents.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/CommonPrimeIndicatorExponents.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Set`, `open scoped ContDiff BigOperators`):
--
--   ```lean
--    theorem first_common_prime_exponents (hpub : PrimitiveResidueHeckeInput)
--       {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1)
--       (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
--       (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
--       (hVnorm : ∀ x, ‖V x‖ ≤ 1)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
--       (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
--       ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
--         ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
--         (∀ r i x, x < 1 → W r i x = 0) → ∃ Y₀ : ℝ,
--         ∀ (r : γ) (Y N : ℝ) (X : ι → ℝ) (q : ι → Eisenstein)
--         (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset Eisenstein),
--         Y₀ ≤ Y → 1 ≤ Real.log Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) →
--         (∀ i, (2*Y)^c < X i) → (∀ i, X i ≤ Y^2) → (∀ i, q i ≠ 0) →
--         (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
--         (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(721/2000:ℝ)) →
--         (∀ a ∈ P, gramDyad N a) →
--         (∑ a ∈ P, ‖primaryPrimeIndicatorTuple a 1 q η t (W r) X V Y‖^2) ≤
--           Y^(7/3-ε)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.GammaInverseFiniteOrder`, `OAI.CubicFirstMoment.GammaQuotientStripBound` and `OAI.CubicFirstMoment.UniformLogWeights` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.gramDyad` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.PrimitiveResidueHeckeInput` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.primaryPrimeIndicatorTuple` (definitions bundle `OAIQ096A010` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.Residues`, `OAI.CubicFirstMoment.modulus` and `OAI.CubicFirstMoment.norm` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.first_unweighted_structured_moment` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/CommonPrimeIndicatorExponents.lean (declaration OAI.CubicFirstMoment.first_common_prime_exponents)

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
open scoped ContDiff BigOperators
namespace CubicFirstMoment
variable {γ ι : Type*} [Fintype ι] [DecidableEq ι]

 theorem first_common_prime_exponents (hpub : PrimitiveResidueHeckeInput)
    {c : ℝ} (hc : 0 < c) (hc₁ : c ≤ 1)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hposV : tsupport V ⊆ Ioi 0)
    (hsmV : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0) (hVhi : ∀ x, 2 < x → V x = 0)
    (hVnorm : ∀ x, ‖V x‖ ≤ 1)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧
      ∀ (W : γ → ι → ℝ → ℂ), UniformLogWeights (fun z : γ × ι => W z.1 z.2) →
      (∀ r i x, x < 1 → W r i x = 0) → ∃ Y₀ : ℝ,
      ∀ (r : γ) (Y N : ℝ) (X : ι → ℝ) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset Eisenstein),
      Y₀ ≤ Y → 1 ≤ Real.log Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) →
      (∀ i, (2*Y)^c < X i) → (∀ i, X i ≤ Y^2) → (∀ i, q i ≠ 0) →
      (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(721/2000:ℝ)) →
      (∀ a ∈ P, gramDyad N a) →
      (∑ a ∈ P, ‖primaryPrimeIndicatorTuple a 1 q η t (W r) X V Y‖^2) ≤
        Y^(7/3-ε) := by
  sorry

end CubicFirstMoment

end

end OAI
end
