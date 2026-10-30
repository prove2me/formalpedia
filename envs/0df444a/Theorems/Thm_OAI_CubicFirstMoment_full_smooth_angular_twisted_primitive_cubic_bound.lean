-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_full_smooth_angular_twisted_primitive_cubic_bound
-- name    : OAI.CubicFirstMoment.full_smooth_angular_twisted_primitive_cubic_bound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-10-30T03:59:46.940238+00:00
-- url     : https://prove2.me/theorems/6ef08142-9f0d-4dbd-bfc7-9366601170e2
-- title:
--   OAI.CubicFirstMoment.full_smooth_angular_twisted_primitive_cubic_bound: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.full_smooth_angular_twisted_primitive_cubic_bound` of [lean/OAI/NumberTheory/CubicMoment/Angular/AngularTwistedSmoothBound.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularTwistedSmoothBound.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open Set`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem full_smooth_angular_twisted_primitive_cubic_bound (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
--       {ε : ℝ} (hε : 0 < ε) (W : ℝ → ℂ) (hW : HasCompactSupport W)
--       (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
--       {δ : ℝ} (hδ : 0 < δ) (H R : ℝ)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
--       (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
--       ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
--         ∀ (P : Finset Eisenstein) (b : Eisenstein) (d : Eisenstein → Eisenstein)
--         (ψ : (a : Eisenstein) → MulChar (Residues (d a)) ℂ)
--         (r : Eisenstein) (η : MulChar (Residues r) ℂ) (N Y Z J t : ℝ),
--         primary b → Squarefree b → r ≠ 0 →
--         (AngularUnitCompatible r η ℓ) →
--         (∀ a ∈ P, IsCoprime (a*b) r) → 1 ≤ N → 1 ≤ Y → 1 ≤ Z → 1 ≤ J →
--         Z ≤ Y^H → J ≤ Y^H →
--         (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b) →
--         (∀ a ∈ P, d a ≠ 0) → (∀ a ∈ P, PrimitiveResidueCharacter (d a) (ψ a)) →
--         (∀ a ∈ P, ℓ ≠ 0 ∨ ψ a ≠ 1) →
--         (∀ a ∈ P, AngularUnitCompatible (d a) (ψ a) ℓ) →
--         (∀ a ∈ P, ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
--           ψ a (Ideal.Quotient.mk (modulus (d a)) x) =
--             mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)) →
--         (∀ a ∈ P, ((residueHeckeScale (d a))^2*(1+|t|)^2)/(Z*J) ≤ Y^(-δ)) →
--         (∑ a ∈ P, ‖∑' ν, angularResidueIdealChar (d a) (ψ a) ℓ ν*
--           mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)‖^2) ≤
--           C*Z*
--             (N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ))*norm (3*r)^ε + D*P.card*Y^(-2*R)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound`, `OAI.CubicFirstMoment.EisensteinIdealExponent` and `OAI.CubicFirstMoment.mixedCubic` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.GammaInverseFiniteOrder` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.mellinPhase` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.AngularUnitCompatible` and `OAI.CubicFirstMoment.idealExponentNorm` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.PrimitiveAngularHeckeInput`, `OAI.CubicFirstMoment.PrimitiveResidueCharacter`, `OAI.CubicFirstMoment.angularResidueIdealChar` and `OAI.CubicFirstMoment.residueHeckeScale` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.Residues`, `OAI.CubicFirstMoment.modulus`, `OAI.CubicFirstMoment.norm` and `OAI.CubicFirstMoment.primary` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI.CubicFirstMoment.angular_balanced_smooth_product_neighborhood`, `OAI_CubicFirstMoment_angular_dominant_balanced_full_factor_neighborhood`, `OAI_CubicFirstMoment_angular_dominant_first_full_factor_neighborhood` and `OAI.CubicFirstMoment.angular_first_unsplit_tuple_neighborhood` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularTwistedSmoothBound.lean (declaration OAI.CubicFirstMoment.full_smooth_angular_twisted_primitive_cubic_bound)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A007

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment

theorem full_smooth_angular_twisted_primitive_cubic_bound (hpub : PrimitiveAngularHeckeInput) (ℓ : ℤ)
    {ε : ℝ} (hε : 0 < ε) (W : ℝ → ℂ) (hW : HasCompactSupport W)
    (hpos : tsupport W ⊆ Ioi 0) (hsm : ContDiff ℝ ∞ W)
    {δ : ℝ} (hδ : 0 < δ) (H R : ℝ)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ (P : Finset Eisenstein) (b : Eisenstein) (d : Eisenstein → Eisenstein)
      (ψ : (a : Eisenstein) → MulChar (Residues (d a)) ℂ)
      (r : Eisenstein) (η : MulChar (Residues r) ℂ) (N Y Z J t : ℝ),
      primary b → Squarefree b → r ≠ 0 →
      (AngularUnitCompatible r η ℓ) →
      (∀ a ∈ P, IsCoprime (a*b) r) → 1 ≤ N → 1 ≤ Y → 1 ≤ Z → 1 ≤ J →
      Z ≤ Y^H → J ≤ Y^H →
      (∀ a ∈ P, primary a ∧ Squarefree a ∧ norm a ≤ N ∧ IsCoprime a b) →
      (∀ a ∈ P, d a ≠ 0) → (∀ a ∈ P, PrimitiveResidueCharacter (d a) (ψ a)) →
      (∀ a ∈ P, ℓ ≠ 0 ∨ ψ a ≠ 1) →
      (∀ a ∈ P, AngularUnitCompatible (d a) (ψ a) ℓ) →
      (∀ a ∈ P, ∀ x : Eisenstein, primary x → IsCoprime (a*b*r) x →
        ψ a (Ideal.Quotient.mk (modulus (d a)) x) =
          mixedCubic a b x*η (Ideal.Quotient.mk (modulus r) x)) →
      (∀ a ∈ P, ((residueHeckeScale (d a))^2*(1+|t|)^2)/(Z*J) ≤ Y^(-δ)) →
      (∑ a ∈ P, ‖∑' ν, angularResidueIdealChar (d a) (ψ a) ℓ ν*
        mellinPhase t (idealExponentNorm ν)*W (idealExponentNorm ν/Z)‖^2) ≤
        C*Z*
          (N*(2*J))^ε*(N+2*J+(N*(2*J))^(2/3:ℝ))*norm (3*r)^ε + D*P.card*Y^(-2*R) := by
  sorry

end CubicFirstMoment

end

end OAI
end
