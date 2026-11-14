-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_cyclic_subfield_order_of_unique_character
-- name    : OAI.DukePrimeDegree.cyclic_subfield_order_of_unique_character
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:55:15.27819+00:00
-- url     : https://prove2.me/theorems/a8abb078-4dfa-4376-a8bf-245e78250487
-- title:
--   OAI.DukePrimeDegree.cyclic_subfield_order_of_unique_character: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.cyclic_subfield_order_of_unique_character` of [lean/OAI/NumberTheory/DukePrimeDegree/Arithmetic/CyclicSubfields.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Arithmetic/CyclicSubfields.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open Module Filter Set`, `open scoped NumberField BigOperators Classical Topology`, `open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter`):
--
--   ```lean
--   theorem cyclic_subfield_order_of_unique_character
--       (L : IntermediateField F E) [NumberField.IsTotallyReal L]
--       (σ : OrderedEmbeddings (d + 1) F) (hn : finrank ℚ F = d + 1)
--       (τ : OrderedEmbeddings (e + 1) L) (he : finrank ℚ L = e + 1)
--       (ψ : ((E ≃ₐ[F] E) →* ℂˣ) → EvenRayCharacter F N)
--       (hid : ∀ χ, (ψ χ).idealHom = idealHom F E χ)
--       (hψ : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
--       (hD : (NumberField.discr E).natAbs ∣ N)
--       {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
--       (χ : (E ≃ₐ[F] E) →* ℂˣ)
--       (hχ : meromorphicOrderAt (cyclicHeckeFactor σ hn ψ χ) (β : ℂ) = 1)
--       (hrest : ∀ φ, φ ≠ χ →
--         meromorphicOrderAt (cyclicHeckeFactor σ hn ψ φ) (β : ℂ) = 0) :
--       meromorphicOrderAt (completedThetaXi τ he) (β : ℂ) =
--         if L.fixingSubgroup ≤ χ.ker then 1 else 0
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.EvenRayCharacter`, `OAI.PrimeDegreePackets.GaloisIdealCharacter.idealHom` and `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi` (definitions bundle `OAIQ244Duke011` of this split); `OAI.PrimeDegreePackets.EvenRayCharacter.IsNonprincipal` (definitions bundle `OAIQ244Duke022` of this split); `OAI.DukePrimeDegree.cyclicHeckeFactor` (definitions bundle `OAIQ244Duke044` of this split); `OAI.PrimeDegreePackets.OrderedEmbeddings` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.exists_real_character_of_simple_zeta` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Arithmetic/CyclicSubfields.lean (declaration OAI.DukePrimeDegree.cyclic_subfield_order_of_unique_character)

import Mathlib
import Mathlib.LinearAlgebra.Vandermonde
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke044

section

attribute [-instance] _root_.AlgebraicNumberTheory.numberFieldInRationalSeparableClosure_numberField _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.complexFourthRootField_numberField _root_.GlobalClassFieldTheory.Reciprocity.infinitePlaceComplexificationOverfield_numberField _root_.GlobalClassFieldTheory.Reciprocity.rationalIntermediateFieldNumberField _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseNumberField _root_.KummerTheory.rationalCyclotomicLevel_numberField _root_.LocalFieldTheory.DiscreteValuationField.CompleteDVF.higherPrincipalUnitGroup.Internal.principalUnitQuotientCarrier_finite _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseNontriviallyNormedField _root_.finiteLocalUnitsOpen _root_.finiteNormalClosure_numberField _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Module Filter Set
open scoped NumberField BigOperators Classical Topology

namespace DukePrimeDegree

open PrimeDegreePackets PrimeDegreePackets.GaloisIdealCharacter
  PrimeDegreePackets.HeckeMellin

variable {F E : Type*} [Field F] [NumberField F] [Field E] [NumberField E]
variable [Algebra F E] [FiniteDimensional F E] [IsGalois F E]
variable [IsCyclic (E ≃ₐ[F] E)]
attribute [local instance] IsCyclic.commGroup

variable [NumberField.IsTotallyReal F] [NumberField.IsTotallyReal E]
variable {d e N : ℕ} [NeZero N]

omit [NumberField.IsTotallyReal E] in
theorem cyclic_subfield_order_of_unique_character
    (L : IntermediateField F E) [NumberField.IsTotallyReal L]
    (σ : OrderedEmbeddings (d + 1) F) (hn : finrank ℚ F = d + 1)
    (τ : OrderedEmbeddings (e + 1) L) (he : finrank ℚ L = e + 1)
    (ψ : ((E ≃ₐ[F] E) →* ℂˣ) → EvenRayCharacter F N)
    (hid : ∀ χ, (ψ χ).idealHom = idealHom F E χ)
    (hψ : ∀ χ, χ ≠ 1 → (ψ χ).IsNonprincipal)
    (hD : (NumberField.discr E).natAbs ∣ N)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (χ : (E ≃ₐ[F] E) →* ℂˣ)
    (hχ : meromorphicOrderAt (cyclicHeckeFactor σ hn ψ χ) (β : ℂ) = 1)
    (hrest : ∀ φ, φ ≠ χ →
      meromorphicOrderAt (cyclicHeckeFactor σ hn ψ φ) (β : ℂ) = 0) :
    meromorphicOrderAt (completedThetaXi τ he) (β : ℂ) =
      if L.fixingSubgroup ≤ χ.ker then 1 else 0 := by
  sorry

end DukePrimeDegree

end

end OAI
end
