-- Prove2me | Theorems.Thm_OAI_PrimeDegreePackets_signedLabel_siegelTransform_lintegral
-- name    : OAI.PrimeDegreePackets.signedLabel_siegelTransform_lintegral
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:53:56.567292+00:00
-- url     : https://prove2.me/theorems/32fb201e-423c-4466-8bda-e8aa6655f7c9
-- title:
--   OAI.PrimeDegreePackets.signedLabel_siegelTransform_lintegral: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PrimeDegreePackets.signedLabel_siegelTransform_lintegral` of [lean/OAI/NumberTheory/PrimePackets/ZetaResidues.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/ZetaResidues.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PrimeDegreePackets`, with `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal`, `open MeasureTheory Filter Set Module`, `open scoped TensorProduct`, `open Set Module`, `open MeasureTheory Set`, `open scoped ENNReal`, `open IsDiscreteValuationRing IsLocalRing`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set IsDiscreteValuationRing`, `open Filter`, `open scoped BigOperators Topology`, `open NumberField`, `open scoped NumberField nonZeroDivisors`, `open scoped BigOperators ArithmeticFunction.zeta`, `open Finset`, `open scoped BigOperators Classical ArithmeticFunction.Moebius`, `open Finset Nat ArithmeticFunction BoundingSieve`, `open scoped BigOperators Classical`, `open Finset Nat`, `open scoped BigOperators`, `open Filter Topology`, `open scoped nonZeroDivisors`, `open Ideal NumberField Finset UniqueFactorizationMonoid`, `open Filter Set Topology NumberField`, `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors`, `open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace`, `open scoped NumberField nonZeroDivisors`, `open scoped Pointwise`, `open FractionalIdeal`):
--
--   ```lean
--   theorem signedLabel_siegelTransform_lintegral {d : ℕ} {K : Type*} [Field K] [NumberField K]
--       [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
--       (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
--       (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
--       [Fintype (SignedGlobalLabel M I)] [Fintype (globalLabels M I)]
--       {t : Set (LogCoordinates d)} (ht : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) t volume)
--       (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
--       (∫⁻ u in t, ∑ x : SignedGlobalLabel M I,
--         siegelTransform f (orbitMap (signedGlobalLabelPoint M σ hodd I x) u)) =
--         (Nat.card (globalLabels M I) : ℝ≥0∞) * (2 *
--         ∑' J : integralIdealClassFiber I, globalIdealWeight M J.1 *
--           productFiberIntegral f ((FractionalIdeal.absNorm J.1.val : ℝ) /
--             ((saturationIndex M : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)|)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.SignedGlobalLabel`, `OAI.PrimeDegreePackets.globalLabels` and `OAI.PrimeDegreePackets.orderedLogSubgroup` (definitions bundle `OAIQ244Duke011` of this split); `OAI.PrimeDegreePackets.integralIdealClassFiber` (definitions bundle `OAIQ244Duke012` of this split); `OAI.PrimeDegreePackets.saturationIndex` (definitions bundle `OAIQ244Duke023` of this split); `OAI.PrimeDegreePackets.productFiberIntegral` and `OAI.PrimeDegreePackets.siegelTransform` (definitions bundle `OAIQ244Duke024` of this split); `OAI.PrimeDegreePackets.globalIdealWeight` and `OAI.PrimeDegreePackets.signedGlobalLabelPoint` (definitions bundle `OAIQ244Duke036` of this split); `OAI.PrimeDegreePackets.FullLattice`, `OAI.PrimeDegreePackets.LogCoordinates`, `OAI.PrimeDegreePackets.OrderedEmbeddings` and `OAI.PrimeDegreePackets.orbitMap` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proofs of `OAI.PrimeDegreePackets.packet_limit_ball_bound_of_zeta_scale` and `OAI.PrimeDegreePackets.packet_tight_of_zeta_scale` of this split import it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/ZetaResidues.lean (declaration OAI.PrimeDegreePackets.signedLabel_siegelTransform_lintegral)

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036

section

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.KummerTheory.primeCyclotomicBaseFiniteDimensional _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.diagonalLogAction_continuous _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.CyclicCohomology.binaryCoefficientFamilyCommGroup _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
open MeasureTheory Set
open scoped ENNReal
open IsDiscreteValuationRing IsLocalRing
open scoped ENNReal BigOperators
open MeasureTheory Set IsDiscreteValuationRing
open Filter
open scoped BigOperators Topology
open NumberField
open scoped NumberField nonZeroDivisors
open scoped BigOperators ArithmeticFunction.zeta
open Finset
open scoped BigOperators Classical ArithmeticFunction.Moebius
open Finset Nat ArithmeticFunction BoundingSieve
open scoped BigOperators Classical
open Finset Nat
open scoped BigOperators
open Filter Topology
open scoped nonZeroDivisors
open Ideal NumberField Finset UniqueFactorizationMonoid
open Filter Set Topology NumberField

open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace
namespace PrimeDegreePackets

open scoped NumberField nonZeroDivisors

open scoped Pointwise

open FractionalIdeal

theorem signedLabel_siegelTransform_lintegral {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (M : FullLattice (d+1) K) (σ : OrderedEmbeddings (d+1) K)
    (hn : Module.finrank ℚ K = d+1) (hodd : Odd (d+1))
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
    [Fintype (SignedGlobalLabel M I)] [Fintype (globalLabels M I)]
    {t : Set (LogCoordinates d)} (ht : IsAddFundamentalDomain (orderedLogSubgroup σ ⊤) t volume)
    (f : (Fin (d+1) → ℝ) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ u in t, ∑ x : SignedGlobalLabel M I,
      siegelTransform f (orbitMap (signedGlobalLabelPoint M σ hodd I x) u)) =
      (Nat.card (globalLabels M I) : ℝ≥0∞) * (2 *
      ∑' J : integralIdealClassFiber I, globalIdealWeight M J.1 *
        productFiberIntegral f ((FractionalIdeal.absNorm J.1.val : ℝ) /
          ((saturationIndex M : ℝ) * Real.sqrt |(NumberField.discr K : ℝ)|))) := by
  sorry

end PrimeDegreePackets
end
end

end OAI
end
