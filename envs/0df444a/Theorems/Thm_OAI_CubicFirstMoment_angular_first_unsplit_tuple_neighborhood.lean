-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_angular_first_unsplit_tuple_neighborhood
-- name    : OAI.CubicFirstMoment.angular_first_unsplit_tuple_neighborhood
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:15:37.050685+00:00
-- url     : https://prove2.me/theorems/7199e108-efdc-4b80-9ac8-ba28a2309b9d
-- title:
--   OAI.CubicFirstMoment.angular_first_unsplit_tuple_neighborhood: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.angular_first_unsplit_tuple_neighborhood` of [lean/OAI/NumberTheory/CubicMoment/Angular/AngularFirstUnsplitNeighborhood.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularFirstUnsplitNeighborhood.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open MeasureTheory Set`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem angular_first_unsplit_tuple_neighborhood (hpub : PrimitiveAngularHeckeInput)
--       (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
--       (hsm : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0)
--       (hVhi : ∀ x, 2 < x → V x = 0)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
--       (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
--       ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y N : ℝ)
--         (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
--         (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset Eisenstein),
--         Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) → F ≤ 2*Y → (∀ i, ShortArithmeticFactor F (A i)) →
--         (∀ i, q i ≠ 0) → (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
--         (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) →
--         (∀ a ∈ P, gramDyad N a) →
--         (∑ a ∈ P, ‖primaryAngularUnsplitTuple ℓ A a 1 q η t V Y‖^2) ≤ Y^(7/3-ε)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.AngularGammaQuotientStripBound` and `OAI.CubicFirstMoment.EisensteinArithmeticFunction` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.GammaInverseFiniteOrder` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.AngularUnitCompatible` and `OAI.CubicFirstMoment.ShortArithmeticFactor` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.gramDyad` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.PrimitiveAngularHeckeInput` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.primaryAngularUnsplitTuple` (definitions bundle `OAIQ096A015` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.Residues`, `OAI.CubicFirstMoment.modulus` and `OAI.CubicFirstMoment.norm` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proof of `OAI.CubicFirstMoment.angular_exceptional_residual_moment` of this split imports it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Angular/AngularFirstUnsplitNeighborhood.lean (declaration OAI.CubicFirstMoment.angular_first_unsplit_tuple_neighborhood)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A015

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeCubeRootCoverGroup_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalGroup_countable _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaRelativeSubgroup_finiteIndex _root_.OAI.CubicFirstMoment.cubicThetaRelativeTransversal_finite _root_.OAI.CubicFirstMoment.shortBranchIndex_decidableEq _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable (ℓ : ℤ)
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem angular_first_unsplit_tuple_neighborhood (hpub : PrimitiveAngularHeckeInput)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V) (hVlo : ∀ x, x < 1 → V x = 0)
    (hVhi : ∀ x, 2 < x → V x = 0)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)+|(ℓ:ℝ)|/2) (2+|(ℓ:ℝ)|/2))
    (hGQ : ∀ m : ℕ, AngularGammaQuotientStripBound (|(ℓ:ℝ)|/2) (1/2-(m:ℝ))) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y N : ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset Eisenstein),
      Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) → F ≤ 2*Y → (∀ i, ShortArithmeticFactor F (A i)) →
      (∀ i, q i ≠ 0) → (∀ i, AngularUnitCompatible (q i) (η i) ℓ) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) →
      (∀ a ∈ P, gramDyad N a) →
      (∑ a ∈ P, ‖primaryAngularUnsplitTuple ℓ A a 1 q η t V Y‖^2) ≤ Y^(7/3-ε) := by
  sorry

end CubicFirstMoment

end

end OAI
end
