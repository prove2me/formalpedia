-- Prove2me | Theorems.Thm_OAI_CubicFirstMoment_first_weighted_tuple_neighborhood
-- name    : OAI.CubicFirstMoment.first_weighted_tuple_neighborhood
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-30T04:00:45.947683+00:00
-- url     : https://prove2.me/theorems/0d5bd52b-60c1-427c-946b-0c66e74d9d08
-- title:
--   OAI.CubicFirstMoment.first_weighted_tuple_neighborhood: intermediate lemma from OpenAI, An unconditional first moment for cubic Gauss sums (result family 023)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CubicFirstMoment.patterson_firstMoment`, `OAI.CubicFirstMoment.patterson_angularComparison` and `OAI.CubicFirstMoment.patterson_angularCancellation`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *An unconditional first moment for cubic Gauss sums (result family 023)*, OpenAI Math Release, September 25, 2026, result family 23, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CubicFirstMoment.first_weighted_tuple_neighborhood` of [lean/OAI/NumberTheory/CubicMoment/Estimates/FirstWeightedNeighborhood.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/FirstWeightedNeighborhood.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CubicFirstMoment`, with `open MeasureTheory Filter Set`, `open scoped BigOperators ContDiff`):
--
--   ```lean
--   theorem first_weighted_tuple_neighborhood (hpub : PrimitiveResidueHeckeInput)
--       (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
--       (hsm : ContDiff ℝ ∞ V)
--       (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
--       (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
--       {D : ℝ} (hD : 0 < D) :
--       ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y N : ℝ) (X : ι → ℝ)
--         (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
--         (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset Eisenstein) (Z : ℝ),
--         Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) → F ≤ D*Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
--         Y/D ≤ ∏ i, X i → (∏ i, X i) ≤ D*Y →
--         (∀ i, q i ≠ 0) → (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
--         (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) →
--         (∀ a ∈ P, gramDyad N a) → 0 < Z →
--         (∑ a ∈ P, ‖primaryShortTupleSum X A a 1 q η
--           (fun _ => normPartitionWeight) t V Z‖^2) ≤ Y^(7/3-ε)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CubicFirstMoment.EisensteinArithmeticFunction` (definitions bundle `OAIQ096A000` of this split); `OAI.CubicFirstMoment.GammaInverseFiniteOrder` and `OAI.CubicFirstMoment.GammaQuotientStripBound` (definitions bundle `OAIQ096A001` of this split); `OAI.CubicFirstMoment.normPartitionWeight` (definitions bundle `OAIQ096A002` of this split); `OAI.CubicFirstMoment.ShortArithmeticFactor` (definitions bundle `OAIQ096A004` of this split); `OAI.CubicFirstMoment.gramDyad` (definitions bundle `OAIQ096A005` of this split); `OAI.CubicFirstMoment.PrimitiveResidueHeckeInput` (definitions bundle `OAIQ096A007` of this split); `OAI.CubicFirstMoment.primaryShortTupleSum` (definitions bundle `OAIQ096A010` of this split); `OAI.CubicFirstMoment.Eisenstein`, `OAI.CubicFirstMoment.Residues`, `OAI.CubicFirstMoment.modulus` and `OAI.CubicFirstMoment.norm` (the published bundle `Def_PattersonFirstMoment`).
--
--   **Used by.** The proofs of `OAI_CubicFirstMoment_first_common_coordinate_exponents` and `OAI.CubicFirstMoment.first_common_prime_exponents` of this split import it.
-- source:
--   OpenAI, An unconditional first moment for cubic Gauss sums (result family 023), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 23; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/An-unconditional-first-moment-for-cubic-Gauss-sums-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/CubicMoment/Estimates/FirstWeightedNeighborhood.lean (declaration OAI.CubicFirstMoment.first_weighted_tuple_neighborhood)

import Mathlib
import Definitions.Def_PattersonFirstMoment
import Definitions.Def_OAIQ096A007
import Definitions.Def_OAIQ096A010

section

attribute [-instance] _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaFullPointAction_properlyDiscontinuous _root_.OAI.CubicFirstMoment.cubicThetaPrimeRootCover_measurableSpace _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_continuous _root_.OAI.CubicFirstMoment.cubicThetaPrincipalPointAction_free _root_.OAI.CubicFirstMoment.cubicThetaQuotient_borelSpace _root_.OAI.CubicFirstMoment.cubicThetaQuotient_measurableSpace _root_.OAI.CubicFirstMoment.shortBranchIndex_fintype _root_.W21.instNorm _root_.OAI.CubicFirstMoment.instNontrivialResiduesOfNatSubtypeComplexMemSubalgebraIntEisenstein _root_.instMeasurableSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators ContDiff
attribute [local instance] Classical.propDecidable
namespace CubicFirstMoment
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem first_weighted_tuple_neighborhood (hpub : PrimitiveResidueHeckeInput)
    (V : ℝ → ℂ) (hV : HasCompactSupport V) (hpos : tsupport V ⊆ Ioi 0)
    (hsm : ContDiff ℝ ∞ V)
    (hGI : ∀ m : ℕ, GammaInverseFiniteOrder (1/2-(m:ℝ)) 2)
    (hGQ : ∀ m : ℕ, GammaQuotientStripBound (1/2-(m:ℝ)))
    {D : ℝ} (hD : 0 < D) :
    ∃ κ : ℝ, 0 < κ ∧ κ ≤ 1/10000 ∧ ∃ ε : ℝ, 0 < ε ∧ ∃ Y₀ : ℝ, ∀ (F Y N : ℝ) (X : ι → ℝ)
      (A : ι → EisensteinArithmeticFunction) (q : ι → Eisenstein)
      (η : (i : ι) → MulChar (Residues (q i)) ℂ) (t : ι → ℝ) (P : Finset Eisenstein) (Z : ℝ),
      Y₀ ≤ Y → Y^(1-κ) ≤ N → N ≤ Y^(1+κ) → F ≤ D*Y → (∀ i, ShortArithmeticFactor F (A i)) → (∀ i, 1 ≤ X i) →
      Y/D ≤ ∏ i, X i → (∏ i, X i) ≤ D*Y →
      (∀ i, q i ≠ 0) → (∀ i, ∀ e : Eisensteinˣ, η i (Ideal.Quotient.mk (modulus (q i)) e) = 1) →
      (∀ i, norm (q i) ≤ Y^(1/100000:ℝ)) → (∀ i, |t i| ≤ Y^(361/1000:ℝ)) →
      (∀ a ∈ P, gramDyad N a) → 0 < Z →
      (∑ a ∈ P, ‖primaryShortTupleSum X A a 1 q η
        (fun _ => normPartitionWeight) t V Z‖^2) ≤ Y^(7/3-ε) := by
  sorry

end CubicFirstMoment

end

end OAI
end
