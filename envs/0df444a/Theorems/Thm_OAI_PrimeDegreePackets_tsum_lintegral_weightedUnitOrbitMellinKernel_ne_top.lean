-- Prove2me | Theorems.Thm_OAI_PrimeDegreePackets_tsum_lintegral_weightedUnitOrbitMellinKernel_ne_top
-- name    : OAI.PrimeDegreePackets.tsum_lintegral_weightedUnitOrbitMellinKernel_ne_top
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:49:33.946737+00:00
-- url     : https://prove2.me/theorems/84343954-63e0-4330-bdcb-e7ba53d6ad0a
-- title:
--   OAI.PrimeDegreePackets.tsum_lintegral_weightedUnitOrbitMellinKernel_ne_top: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PrimeDegreePackets.tsum_lintegral_weightedUnitOrbitMellinKernel_ne_top` of [lean/OAI/NumberTheory/PrimePackets/UnitOrbitIntegrals.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/UnitOrbitIntegrals.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PrimeDegreePackets`, with `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal`, `open MeasureTheory Filter Set Module`, `open scoped TensorProduct`, `open Set Module`, `open MeasureTheory Set`, `open scoped ENNReal`, `open IsDiscreteValuationRing IsLocalRing`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set IsDiscreteValuationRing`, `open Filter`, `open scoped BigOperators Topology`, `open NumberField`, `open scoped NumberField nonZeroDivisors`, `open scoped BigOperators ArithmeticFunction.zeta`, `open Finset`, `open scoped BigOperators Classical ArithmeticFunction.Moebius`, `open Finset Nat ArithmeticFunction BoundingSieve`, `open scoped BigOperators Classical`, `open Finset Nat`, `open scoped BigOperators`, `open Filter Topology`, `open scoped nonZeroDivisors`, `open Ideal NumberField Finset UniqueFactorizationMonoid`, `open Filter Set Topology NumberField`, `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors`, `open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace`, `open Filter Set Topology`, `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace`, `open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix`, `open MeasureTheory Filter Set Module TopologicalSpace`, `open MeasureTheory Filter Set`, `open scoped BigOperators Topology ENNReal`, `open scoped BigOperators Topology ENNReal Classical`, `open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise`, `open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise`, `open scoped BigOperators Topology ENNReal Classical Matrix Pointwise`, `open scoped BigOperators Topology ENNReal Classical Matrix`, `open MeasureTheory ProbabilityTheory Filter Set`, `open Set Filter`, `open scoped Topology`, `open scoped Classical`, `open scoped Topology ENNReal Classical`, `open scoped ENNReal Classical`, `open MeasureTheory Set Topology UniformSpace TopologicalSpace`, `open scoped ENNReal Topology`, `open MeasureTheory Filter Set Matrix`, `open scoped Topology Classical`, `open scoped Matrix Classical`, `open scoped Topology Classical Matrix`, `open scoped Classical Pointwise`, `open scoped Topology Classical ENNReal`, `open scoped Matrix Topology Classical`, `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Matrix Topology Classical ENNReal ProbabilityTheory`, `open scoped ENNReal ProbabilityTheory`, `open Set Filter Topology`, `open Set Filter Topology MeasureTheory`, `open MeasureTheory Set Filter Topology`, `open MeasureTheory ProbabilityTheory Set Filter Topology`, `open scoped Matrix ENNReal NNReal ProbabilityTheory`, `open MeasureTheory`, `open scoped BigOperators ENNReal`, `open NumberField Finset`, `open NumberField Filter Set Topology`, `open MeasureTheory ProbabilityTheory Matrix`, `open scoped Classical BigOperators ENNReal`, `open MeasureTheory Set Filter Topology Module`, `open scoped BigOperators SchwartzMap`, `open MeasureTheory Set Filter Topology Module WithLp`, `open scoped BigOperators SchwartzMap ZeroAtInfty`, `open scoped FourierTransform`, `open scoped BigOperators SchwartzMap FourierTransform`, `open scoped BigOperators FourierTransform`, `open MeasureTheory Set Filter Topology Module WithLp Asymptotics`, `open Module WithLp MeasureTheory`, `open scoped BigOperators Matrix`, `open Module MeasureTheory`, `open MeasureTheory Module WithLp`, `open scoped BigOperators NumberField nonZeroDivisors ENNReal`, `open Complex Set Metric Filter`, `open Complex Set Metric Filter MeromorphicOn`, `open scoped Topology ComplexConjugate`, `open MeasureTheory Set Filter`, `open scoped ENNReal BigOperators Topology`, `open MeasureTheory Set Module`, `open scoped BigOperators ENNReal NumberField nonZeroDivisors`, `open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology`, `open Set`, `open Filter Set Module MeasureTheory`, `open scoped Topology NumberField`, `open Filter Set Module MeasureTheory WithLp`, `open scoped Topology NumberField BigOperators nonZeroDivisors`, `open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate`, `open MeasureTheory Set Filter Module WithLp`, `open scoped Topology BigOperators NumberField nonZeroDivisors`, `open Complex Set Filter Module`, `open Complex`, `open Complex Set Filter`, `open scoped Topology NumberField ComplexConjugate`, `open scoped Topology NumberField ComplexConjugate Classical`, `open Filter Set Topology Module`, `open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace`, `open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter`, `open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory`, `open scoped Matrix Topology Classical ENNReal`, `open scoped Topology ENNReal`, `open scoped Matrix Topology ENNReal ProbabilityTheory`, `open scoped Topology ENNReal CompactlySupported`, `open MeasureTheory Set Filter TopologicalSpace`, `open Module Set Matrix MeasureTheory Filter`, `open scoped NumberField`, `open CategoryTheory Module`, `open MeasureTheory Module Set Filter`, `open scoped BigOperators ENNReal RealInnerProductSpace`, `open Module Matrix`, `open scoped NumberField BigOperators`, `open Module MeasureTheory Set WithLp`, `open scoped NumberField BigOperators ENNReal`, `open IntermediateField Module`, `open Module IntermediateField`, `open scoped BigOperators NumberField Pointwise`, `open Module IntermediateField Set`, `open MeasureTheory Set Module Filter`, `open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate`, `open Module`, `open MeasureTheory Module`, `open scoped BigOperators Matrix NumberField nonZeroDivisors`, `open scoped BigOperators NumberField nonZeroDivisors`, `open MeasureTheory Module WithLp Set`, `open scoped BigOperators NumberField ENNReal`, `open scoped BigOperators NumberField`, `open scoped BigOperators NumberField ENNReal nonZeroDivisors`, `open HeckeMellin ThetaConstruction`):
--
--   ```lean
--   lemma tsum_lintegral_weightedUnitOrbitMellinKernel_ne_top
--       (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
--       (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (S : Subgroup (𝓞 K)ˣ)
--       {D : Set (LogCoordinates d)}
--       (hD : IsAddFundamentalDomain (orderedLogSubgroup σ S) D volume)
--       (w : integralIdealClassFiber I → ℂ) (hw : ∀ J, ‖w J‖ ≤ 1)
--       {s : ℂ} (hs : 1 < s.re) :
--       (∑' J : integralIdealClassFiber I, ∫⁻ p,
--         ‖w J * unitOrbitMellinKernel σ S (idealElementRepresentative I J).1.1 s p‖ₑ
--           ∂(volume.restrict (Ioi 0)).prod (volume.restrict D)) ≠ ⊤
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.orderedLogSubgroup` (definitions bundle `OAIQ244Duke011` of this split); `OAI.PrimeDegreePackets.integralIdealClassFiber` (definitions bundle `OAIQ244Duke012` of this split); `OAI.PrimeDegreePackets.idealElementRepresentative` (definitions bundle `OAIQ244Duke023` of this split); `OAI.PrimeDegreePackets.unitOrbitMellinKernel` (definitions bundle `OAIQ244Duke024` of this split); `OAI.PrimeDegreePackets.LogCoordinates` and `OAI.PrimeDegreePackets.OrderedEmbeddings` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proofs of `OAI.PrimeDegreePackets.EvenRayCharacter.continued_eq_dirichlet` and `OAI.PrimeDegreePackets.integrable_weightedIdealUnitOrbits` of this split import it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/UnitOrbitIntegrals.lean (declaration OAI.PrimeDegreePackets.tsum_lintegral_weightedUnitOrbitMellinKernel_ne_top)

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke023
import Definitions.Def_OAIQ244Duke024

section

attribute [-instance] _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.DiscreteValuationField.DVF.maximalIdealPowSuccQuotModule _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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
open Filter Set Topology
open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace
open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix
open MeasureTheory Filter Set Module TopologicalSpace
open MeasureTheory Filter Set
open scoped BigOperators Topology ENNReal
open scoped BigOperators Topology ENNReal Classical
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise
open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix Pointwise
open scoped BigOperators Topology ENNReal Classical Matrix
open MeasureTheory ProbabilityTheory Filter Set
open Set Filter
open scoped Topology
open scoped Classical
open scoped Topology ENNReal Classical
open scoped ENNReal Classical
open MeasureTheory Set Topology UniformSpace TopologicalSpace
open scoped ENNReal Topology
open MeasureTheory Filter Set Matrix
open scoped Topology Classical
open scoped Matrix Classical
open scoped Topology Classical Matrix
open scoped Classical Pointwise
open scoped Topology Classical ENNReal
open scoped Matrix Topology Classical
open MeasureTheory ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal ProbabilityTheory
open scoped ENNReal ProbabilityTheory
open Set Filter Topology
open Set Filter Topology MeasureTheory
open MeasureTheory Set Filter Topology
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped Matrix ENNReal NNReal ProbabilityTheory
open MeasureTheory
open scoped BigOperators ENNReal
open NumberField Finset
open NumberField Filter Set Topology
open MeasureTheory ProbabilityTheory Matrix
open scoped Classical BigOperators ENNReal
open MeasureTheory Set Filter Topology Module
open scoped BigOperators SchwartzMap
open MeasureTheory Set Filter Topology Module WithLp
open scoped BigOperators SchwartzMap ZeroAtInfty
open scoped FourierTransform
open scoped BigOperators SchwartzMap FourierTransform
open scoped BigOperators FourierTransform
open MeasureTheory Set Filter Topology Module WithLp Asymptotics
open Module WithLp MeasureTheory
open scoped BigOperators Matrix
open Module MeasureTheory
open MeasureTheory Module WithLp
open scoped BigOperators NumberField nonZeroDivisors ENNReal
open Complex Set Metric Filter
open Complex Set Metric Filter MeromorphicOn
open scoped Topology ComplexConjugate
open MeasureTheory Set Filter
open scoped ENNReal BigOperators Topology
open MeasureTheory Set Module
open scoped BigOperators ENNReal NumberField nonZeroDivisors
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology
open Set
open Filter Set Module MeasureTheory
open scoped Topology NumberField
open Filter Set Module MeasureTheory WithLp
open scoped Topology NumberField BigOperators nonZeroDivisors
open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate
open MeasureTheory Set Filter Module WithLp
open scoped Topology BigOperators NumberField nonZeroDivisors
open Complex Set Filter Module
open Complex
open Complex Set Filter
open scoped Topology NumberField ComplexConjugate
open scoped Topology NumberField ComplexConjugate Classical
open Filter Set Topology Module
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter
open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory
open scoped Matrix Topology Classical ENNReal
open scoped Topology ENNReal
open scoped Matrix Topology ENNReal ProbabilityTheory
open scoped Topology ENNReal CompactlySupported
open MeasureTheory Set Filter TopologicalSpace
open Module Set Matrix MeasureTheory Filter
open scoped NumberField
open CategoryTheory Module
open MeasureTheory Module Set Filter
open scoped BigOperators ENNReal RealInnerProductSpace
open Module Matrix
open scoped NumberField BigOperators
open Module MeasureTheory Set WithLp
open scoped NumberField BigOperators ENNReal
open IntermediateField Module
open Module IntermediateField
open scoped BigOperators NumberField Pointwise
open Module IntermediateField Set
open MeasureTheory Set Module Filter
open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology ComplexConjugate
open Module
open MeasureTheory Module
open scoped BigOperators Matrix NumberField nonZeroDivisors
open scoped BigOperators NumberField nonZeroDivisors
open MeasureTheory Module WithLp Set
open scoped BigOperators NumberField ENNReal
open scoped BigOperators NumberField
open scoped BigOperators NumberField ENNReal nonZeroDivisors
namespace PrimeDegreePackets
open HeckeMellin ThetaConstruction
variable {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K]

lemma tsum_lintegral_weightedUnitOrbitMellinKernel_ne_top
    (σ : OrderedEmbeddings (d+1) K) (hn : finrank ℚ K = d+1)
    (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) (S : Subgroup (𝓞 K)ˣ)
    {D : Set (LogCoordinates d)}
    (hD : IsAddFundamentalDomain (orderedLogSubgroup σ S) D volume)
    (w : integralIdealClassFiber I → ℂ) (hw : ∀ J, ‖w J‖ ≤ 1)
    {s : ℂ} (hs : 1 < s.re) :
    (∑' J : integralIdealClassFiber I, ∫⁻ p,
      ‖w J * unitOrbitMellinKernel σ S (idealElementRepresentative I J).1.1 s p‖ₑ
        ∂(volume.restrict (Ioi 0)).prod (volume.restrict D)) ≠ ⊤ := by
  sorry

end PrimeDegreePackets

end
end

end OAI
end
