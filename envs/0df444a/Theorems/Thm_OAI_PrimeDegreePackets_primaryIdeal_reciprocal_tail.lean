-- Prove2me | Theorems.Thm_OAI_PrimeDegreePackets_primaryIdeal_reciprocal_tail
-- name    : OAI.PrimeDegreePackets.primaryIdeal_reciprocal_tail
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:54:39.998227+00:00
-- url     : https://prove2.me/theorems/fefccb73-41b6-4328-be36-fc65114fba09
-- title:
--   OAI.PrimeDegreePackets.primaryIdeal_reciprocal_tail: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PrimeDegreePackets.primaryIdeal_reciprocal_tail` of [lean/OAI/NumberTheory/PrimePackets/LocalEuler.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/LocalEuler.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PrimeDegreePackets`, with `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal`, `open MeasureTheory Filter Set Module`, `open scoped TensorProduct`, `open Set Module`, `open MeasureTheory Set`, `open scoped ENNReal`, `open IsDiscreteValuationRing IsLocalRing`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set IsDiscreteValuationRing`, `open Filter`, `open scoped BigOperators Topology`, `open NumberField`, `open scoped NumberField nonZeroDivisors`, `open scoped BigOperators ArithmeticFunction.zeta`, `open Finset`, `open scoped BigOperators Classical ArithmeticFunction.Moebius`, `open Finset Nat ArithmeticFunction BoundingSieve`, `open scoped BigOperators Classical`, `open Finset Nat`, `open scoped BigOperators`, `open Filter Topology`, `open scoped nonZeroDivisors`, `open Ideal NumberField Finset UniqueFactorizationMonoid`, `open NumberField Finset`, `open scoped BigOperators ENNReal nonZeroDivisors`):
--
--   ```lean
--   theorem primaryIdeal_reciprocal_tail {n : ℕ} {K : Type*} [Field K] [NumberField K]
--       (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (hn0 : 0 < n)
--       (Q : ℝ) (hQ : 0 < Q) (hqQ : (saturationIndex M : ℝ) ≤ Q) :
--       let s : ℝ := 1 / (2 * (n : ℝ))
--       let hε : 0 < s / 16 := by dsimp [s] <;> positivity
--       (∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
--         if ENNReal.ofReal Q ^ (1/8 : ℝ) < (Ideal.absNorm I.1.1 : ℝ≥0∞)
--         then globalIdealWeight M (nonzeroIntegralIdealUnit I.1) / (Ideal.absNorm I.1.1 : ℝ≥0∞)
--         else 0) ≤
--           (saturationIndex M : ℝ≥0∞)⁻¹ *
--             ENNReal.ofReal (localProductConstant n (s / 16) hε) *
--             ENNReal.ofReal Q ^ (-s / 16)
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.nonzeroIntegralIdealUnit` and `OAI.PrimeDegreePackets.primaryIntegralIdeals` (definitions bundle `OAIQ244Duke012` of this split); `OAI.PrimeDegreePackets.saturationIndex` (definitions bundle `OAIQ244Duke023` of this split); `OAI.PrimeDegreePackets.localProductConstant` (definitions bundle `OAIQ244Duke024` of this split); `OAI.PrimeDegreePackets.globalIdealWeight` (definitions bundle `OAIQ244Duke036` of this split); `OAI.PrimeDegreePackets.FullLattice` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.PrimeDegreePackets.weightedIdeal_realInterval_of_zeta_scale` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/LocalEuler.lean (declaration OAI.PrimeDegreePackets.primaryIdeal_reciprocal_tail)

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036

section

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.globalLabelsMulAction _root_.OAI.PrimeDegreePackets.matrixLocallyCompact _root_.OAI.PrimeDegreePackets.matrixSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.isDomain _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
attribute [-simp] _root_.ClassFormation.chosenOrbitClassEquiv_symm_apply _root_.CyclicCohomology.additive_toMul_finset_sum_units _root_.IsDiscreteValuationRing.addVal_ringEquiv _root_.KummerTheory.RadicalDatum.smul_algebraMap_unit _root_.LocalFieldTheory.powMonoidHom_range_one_mem _root_.LocalFieldTheory.residueField_algebraMap_residue _root_.OAI.DukePrimeDegree.FullLattice.toPacket_carrier _root_.OAI.PrimeDegreePackets.ThetaConstruction.schwartzCM_apply _root_.OAI.PrimeDegreePackets.globalLabels_smul_val _root_.infinitePlace_mult_smul
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

namespace PrimeDegreePackets
open NumberField Finset
open scoped BigOperators ENNReal nonZeroDivisors

theorem primaryIdeal_reciprocal_tail {n : ℕ} {K : Type*} [Field K] [NumberField K]
    (M : FullLattice n K) (hn : Module.finrank ℚ K = n) (hn0 : 0 < n)
    (Q : ℝ) (hQ : 0 < Q) (hqQ : (saturationIndex M : ℝ) ≤ Q) :
    let s : ℝ := 1 / (2 * (n : ℝ))
    let hε : 0 < s / 16 := by dsimp [s] <;> positivity
    (∑' I : primaryIntegralIdeals K (saturationIndex M).primeFactors,
      if ENNReal.ofReal Q ^ (1/8 : ℝ) < (Ideal.absNorm I.1.1 : ℝ≥0∞)
      then globalIdealWeight M (nonzeroIntegralIdealUnit I.1) / (Ideal.absNorm I.1.1 : ℝ≥0∞)
      else 0) ≤
        (saturationIndex M : ℝ≥0∞)⁻¹ *
          ENNReal.ofReal (localProductConstant n (s / 16) hε) *
          ENNReal.ofReal Q ^ (-s / 16) := by
  sorry

end PrimeDegreePackets

end
end

end OAI
end
