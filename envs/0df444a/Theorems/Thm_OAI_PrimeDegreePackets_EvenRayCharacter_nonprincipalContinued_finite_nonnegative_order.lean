-- Prove2me | Theorems.Thm_OAI_PrimeDegreePackets_EvenRayCharacter_nonprincipalContinued_finite_nonnegative_order
-- name    : OAI.PrimeDegreePackets.EvenRayCharacter.nonprincipalContinued_finite_nonnegative_order
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:57:07.890686+00:00
-- url     : https://prove2.me/theorems/6915a1d8-9d15-4d3f-81dd-f34bac4f76bf
-- title:
--   OAI.PrimeDegreePackets.EvenRayCharacter.nonprincipalContinued_finite_nonnegative_order: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PrimeDegreePackets.EvenRayCharacter.nonprincipalContinued_finite_nonnegative_order` of [lean/OAI/NumberTheory/PrimePackets/RayContinuation.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/RayContinuation.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PrimeDegreePackets.EvenRayCharacter`, with `open Set Module Filter Topology`, `open scoped BigOperators NumberField nonZeroDivisors Classical ComplexConjugate`, `open HeckeMellin ThetaConstruction`):
--
--   ```lean
--   theorem nonprincipalContinued_finite_nonnegative_order {d : ℕ}
--       [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
--       (hn : finrank ℚ K = d+1) (hψ : ψ.IsNonprincipal) (β : ℂ) :
--       ∃ m : ℕ, meromorphicOrderAt (ψ.nonprincipalContinued σ hn) β = (m : WithTop ℤ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.EvenRayCharacter` (definitions bundle `OAIQ244Duke011` of this split); `OAI.PrimeDegreePackets.EvenRayCharacter.IsNonprincipal` (definitions bundle `OAIQ244Duke022` of this split); `OAI.PrimeDegreePackets.EvenRayCharacter.nonprincipalContinued` (definitions bundle `OAIQ244Duke044` of this split); `OAI.PrimeDegreePackets.OrderedEmbeddings` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proofs of `OAI.DukePrimeDegree.exists_real_character_of_simple_zeta` and `OAI.DukePrimeDegree.fixedFieldMultiplicity_le_extension` of this split import it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/RayContinuation.lean (declaration OAI.PrimeDegreePackets.EvenRayCharacter.nonprincipalContinued_finite_nonnegative_order)

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke044

section

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_residueFinite _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.LocalClassFieldTheory.comparisonIntegerRingIsIntegralClosure _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.chosenFinitePlaceBaseNontriviallyNormedField _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Module Filter Topology
open scoped BigOperators NumberField nonZeroDivisors Classical ComplexConjugate
namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
namespace EvenRayCharacter
variable {K : Type*} [Field K] [NumberField K] {N : ℕ}
variable (ψ : EvenRayCharacter K N)

variable [NeZero N]

theorem nonprincipalContinued_finite_nonnegative_order {d : ℕ}
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1) (hψ : ψ.IsNonprincipal) (β : ℂ) :
    ∃ m : ℕ, meromorphicOrderAt (ψ.nonprincipalContinued σ hn) β = (m : WithTop ℤ) := by
  sorry

end EvenRayCharacter
end PrimeDegreePackets

end

end OAI
end
