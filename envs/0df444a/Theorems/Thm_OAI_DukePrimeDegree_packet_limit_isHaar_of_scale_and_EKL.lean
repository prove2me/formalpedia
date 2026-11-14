-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_packet_limit_isHaar_of_scale_and_EKL
-- name    : OAI.DukePrimeDegree.packet_limit_isHaar_of_scale_and_EKL
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:51:53.700623+00:00
-- url     : https://prove2.me/theorems/75d427e6-2b4b-40cb-91a3-88c418899033
-- title:
--   OAI.DukePrimeDegree.packet_limit_isHaar_of_scale_and_EKL: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.packet_limit_isHaar_of_scale_and_EKL` of [lean/OAI/NumberTheory/DukePrimeDegree/MainConditional.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/MainConditional.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open MeasureTheory ProbabilityTheory Filter Set`, `open scoped ENNReal Topology`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem packet_limit_isHaar_of_scale_and_EKL
--       (d : ℕ) (hprime : Nat.Prime (d + 1)) (hthree : 3 ≤ d + 1) (hodd : Odd (d + 1))
--       (Hscale : UniformZetaScaleBound.{u} (d + 1)) (ekl : EKLPrimeInput d)
--       (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
--       [∀ i, NumberField.IsTotallyReal (K i)]
--       (M : ∀ i, PrimeDegreePackets.FullLattice (d + 1) (K i))
--       (σ : ∀ i, OrderedEmbeddings (d + 1) (K i))
--       (hn : ∀ i, Module.finrank ℚ (K i) = d + 1)
--       (hD : Tendsto (fun i => PrimeDegreePackets.multiplierDiscriminant (M i)) atTop atTop)
--       (ν : ProbabilityMeasure (X (d + 1)))
--       (hlim : Tendsto (fun i => packetProbability (M i) (σ i) (hn i) hodd)
--         atTop (𝓝 ν)) : IsHaarProbability (ν : Measure (X (d + 1)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.EKLPrimeInput` (definitions bundle `OAIQ244Duke011` of this split); `OAI.PrimeDegreePackets.UniformZetaScaleBound` (definitions bundle `OAIQ244Duke012` of this split); `OAI.PrimeDegreePackets.packetProbability` (definitions bundle `OAIQ244Duke036` of this split); `OAI.PrimeDegreePackets.FullLattice`, `OAI.PrimeDegreePackets.G`, `OAI.PrimeDegreePackets.IsHaarProbability`, `OAI.PrimeDegreePackets.OrderedEmbeddings`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.integralGroup`, `OAI.PrimeDegreePackets.multiplierDiscriminant`, `OAI.PrimeDegreePackets.xBorelSpace` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.prime_degree_packet_equidistribution_of_real_zero_exclusion` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/MainConditional.lean (declaration OAI.DukePrimeDegree.packet_limit_isHaar_of_scale_and_EKL)

import Mathlib
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Sequences
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke036

section

attribute [-instance] _root_.GlobalClassFieldTheory.ClassFieldAxiom.finitePlaceAdicCompletion_charZero _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosureAlgebra _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isGalois _root_.GlobalClassFieldTheory.Reciprocity.rationalSeparableClosure_isNormal _root_.KummerTheory.ProfiniteUnitDecomposition.Internal.primeFact _root_.LocalFieldTheory.Padic.padicIsNonarchimedeanLocalField _root_.LocalFieldTheory.finite_powMonoidHom_ker_prod _root_.LocalFieldTheory.finite_powMonoidHom_ker_units _root_.LocalFieldTheory.finite_powMonoidHom_rangeQuotient_prod _root_.OAI.DukePrimeDegree.EliminationChain.futureAmbientKernel_markov _root_.OAI.DukePrimeDegree.EliminationChain.wholeFutureProbabilityKernel_markov _root_.OAI.DukePrimeDegree.InitialRootStep.nextConjugatedKernel_markov _root_.OAI.DukePrimeDegree.initialRemainingErase_standardBorel _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeOrbitQuotientBorelSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientMeasurableSpace _root_.OAI.DukePrimeDegree.latticeOrbitQuotientSecondCountable _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.positiveRootGeneratedGroup_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.RootBox.coordinateMeasure_finite _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.periodSubmodule_addSubgroup_discrete _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.RelativeIdeleGroup.relativeIdeleMulAction _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.adicCompletionProperSpace _root_.finiteLocalUnitsOpen _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Topology

namespace DukePrimeDegree

open PrimeDegreePackets

universe u

theorem packet_limit_isHaar_of_scale_and_EKL
    (d : ℕ) (hprime : Nat.Prime (d + 1)) (hthree : 3 ≤ d + 1) (hodd : Odd (d + 1))
    (Hscale : UniformZetaScaleBound.{u} (d + 1)) (ekl : EKLPrimeInput d)
    (K : ℕ → Type u) [∀ i, Field (K i)] [∀ i, NumberField (K i)]
    [∀ i, NumberField.IsTotallyReal (K i)]
    (M : ∀ i, PrimeDegreePackets.FullLattice (d + 1) (K i))
    (σ : ∀ i, OrderedEmbeddings (d + 1) (K i))
    (hn : ∀ i, Module.finrank ℚ (K i) = d + 1)
    (hD : Tendsto (fun i => PrimeDegreePackets.multiplierDiscriminant (M i)) atTop atTop)
    (ν : ProbabilityMeasure (X (d + 1)))
    (hlim : Tendsto (fun i => packetProbability (M i) (σ i) (hn i) hodd)
      atTop (𝓝 ν)) : IsHaarProbability (ν : Measure (X (d + 1))) := by
  sorry

end DukePrimeDegree

end OAI
end
