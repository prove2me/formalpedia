-- Prove2me | Theorems.Thm_OAI_PrimeDegreePackets_globalContainment_eq_relativeIdealWeight
-- name    : OAI.PrimeDegreePackets.globalContainment_eq_relativeIdealWeight
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:52:01.52205+00:00
-- url     : https://prove2.me/theorems/ce31354a-73bf-4cc3-935c-cefc53f651de
-- title:
--   OAI.PrimeDegreePackets.globalContainment_eq_relativeIdealWeight: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PrimeDegreePackets.globalContainment_eq_relativeIdealWeight` of [lean/OAI/NumberTheory/PrimePackets/PacketAlgebra.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/PacketAlgebra.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PrimeDegreePackets`, with `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal`, `open MeasureTheory Filter Set Module`, `open scoped TensorProduct`, `open Set Module`, `open scoped NumberField Pointwise nonZeroDivisors`, `open NumberField`, `open Topology`, `open scoped Pointwise`, `open Polynomial`, `open scoped NNReal`, `open Polynomial`, `open scoped BigOperators`, `open IsDiscreteValuationRing IsLocalRing Module`, `open MeasureTheory`, `open scoped ENNReal`):
--
--   ```lean
--   theorem globalContainment_eq_relativeIdealWeight
--       {n : ℕ} {K : Type*} [Field K] [NumberField K]
--       (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
--       (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : Kˣ)
--       (ha : (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) :
--       (Nat.card {N : globalLabels M I // (a : K) ∈ N.val} : ℝ≥0∞) / Nat.card (globalLabels M I) =
--         globalIdealWeight M (relativeElementIdeal I a)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.globalLabels` (definitions bundle `OAIQ244Duke011` of this split); `OAI.PrimeDegreePackets.relativeElementIdeal` (definitions bundle `OAIQ244Duke012` of this split); `OAI.PrimeDegreePackets.globalIdealWeight` (definitions bundle `OAIQ244Duke036` of this split); `OAI.PrimeDegreePackets.FullLattice` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.PrimeDegreePackets.signedLabel_siegelTransform_lintegral` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/PacketAlgebra.lean (declaration OAI.PrimeDegreePackets.globalContainment_eq_relativeIdealWeight)

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036

section

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal
open MeasureTheory Filter Set Module

universe u
open scoped TensorProduct
open Set Module
namespace PrimeDegreePackets

open scoped NumberField Pointwise nonZeroDivisors
open NumberField

open Topology
open scoped Pointwise

open Polynomial

open scoped NNReal

open Polynomial
open scoped BigOperators

open IsDiscreteValuationRing IsLocalRing Module

open MeasureTheory
open scoped ENNReal

theorem globalContainment_eq_relativeIdealWeight
    {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (a : Kˣ)
    (ha : (a : K) ∈ (I : FractionalIdeal (𝓞 K)⁰ K)) :
    (Nat.card {N : globalLabels M I // (a : K) ∈ N.val} : ℝ≥0∞) / Nat.card (globalLabels M I) =
      globalIdealWeight M (relativeElementIdeal I a) := by
  sorry

end PrimeDegreePackets
end
end

end OAI
end
