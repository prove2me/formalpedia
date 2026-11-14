-- Prove2me | Theorems.Thm_OAI_PrimeDegreePackets_HeckeMellin_completedThetaXi_eq_totallyReal
-- name    : OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_eq_totallyReal
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:42:22.680206+00:00
-- url     : https://prove2.me/theorems/99a4496c-aebe-45e9-b460-321d37483db4
-- title:
--   OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_eq_totallyReal: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_eq_totallyReal` of [lean/OAI/NumberTheory/PrimePackets/RealMellin.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/RealMellin.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PrimeDegreePackets.HeckeMellin`, with `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal`, `open MeasureTheory Filter Set Module`, `open scoped TensorProduct`, `open Set Module`, `open MeasureTheory Set`, `open scoped ENNReal`, `open IsDiscreteValuationRing IsLocalRing`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set IsDiscreteValuationRing`, `open Filter`, `open scoped BigOperators Topology`, `open NumberField`, `open scoped NumberField nonZeroDivisors`, `open scoped BigOperators ArithmeticFunction.zeta`, `open Finset`, `open scoped BigOperators Classical ArithmeticFunction.Moebius`, `open Finset Nat ArithmeticFunction BoundingSieve`, `open scoped BigOperators Classical`, `open Finset Nat`, `open scoped BigOperators`, `open Filter Topology`, `open scoped nonZeroDivisors`, `open Ideal NumberField Finset UniqueFactorizationMonoid`, `open Filter Set Topology NumberField`, `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors`, `open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace`, `open Filter Set Topology`, `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace`, `open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix`, `open MeasureTheory Filter Set Module TopologicalSpace`, `open MeasureTheory Filter Set`, `open scoped BigOperators Topology ENNReal`, `open scoped BigOperators Topology ENNReal Classical`, `open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise`, `open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise`, `open scoped BigOperators Topology ENNReal Classical Matrix Pointwise`, `open scoped BigOperators Topology ENNReal Classical Matrix`, `open MeasureTheory ProbabilityTheory Filter Set`, `open Set Filter`, `open scoped Topology`, `open scoped Classical`, `open scoped Topology ENNReal Classical`, `open scoped ENNReal Classical`, `open MeasureTheory Set Topology UniformSpace TopologicalSpace`, `open scoped ENNReal Topology`, `open MeasureTheory Filter Set Matrix`, `open scoped Topology Classical`, `open scoped Matrix Classical`, `open scoped Topology Classical Matrix`, `open scoped Classical Pointwise`, `open scoped Topology Classical ENNReal`, `open scoped Matrix Topology Classical`, `open MeasureTheory ProbabilityTheory Set Filter`, `open scoped Matrix Topology Classical ENNReal ProbabilityTheory`, `open scoped ENNReal ProbabilityTheory`, `open Set Filter Topology`, `open Set Filter Topology MeasureTheory`, `open MeasureTheory Set Filter Topology`, `open MeasureTheory ProbabilityTheory Set Filter Topology`, `open scoped Matrix ENNReal NNReal ProbabilityTheory`, `open MeasureTheory`, `open scoped BigOperators ENNReal`, `open NumberField Finset`, `open NumberField Filter Set Topology`, `open MeasureTheory ProbabilityTheory Matrix`, `open scoped Classical BigOperators ENNReal`, `open MeasureTheory Set Filter Topology Module`, `open scoped BigOperators SchwartzMap`, `open MeasureTheory Set Filter Topology Module WithLp`, `open scoped BigOperators SchwartzMap ZeroAtInfty`, `open scoped FourierTransform`, `open scoped BigOperators SchwartzMap FourierTransform`, `open scoped BigOperators FourierTransform`, `open MeasureTheory Set Filter Topology Module WithLp Asymptotics`, `open Module WithLp MeasureTheory`, `open scoped BigOperators Matrix`, `open Module MeasureTheory`, `open MeasureTheory Module WithLp`, `open scoped BigOperators NumberField nonZeroDivisors ENNReal`, `open Complex Set Metric Filter`, `open Complex Set Metric Filter MeromorphicOn`, `open scoped Topology ComplexConjugate`, `open MeasureTheory Set Filter`, `open scoped ENNReal BigOperators Topology`, `open MeasureTheory Set Module`, `open scoped BigOperators ENNReal NumberField nonZeroDivisors`, `open scoped BigOperators ENNReal NumberField nonZeroDivisors Topology`, `open Set`, `open Filter Set Module MeasureTheory`, `open scoped Topology NumberField`, `open Filter Set Module MeasureTheory WithLp`, `open scoped Topology NumberField BigOperators nonZeroDivisors`, `open scoped Topology NumberField BigOperators nonZeroDivisors ComplexConjugate`, `open MeasureTheory Set Filter Module WithLp`, `open scoped Topology BigOperators NumberField nonZeroDivisors`, `open Complex Set Filter Module`, `open Complex`, `open Complex Set Filter`, `open scoped Topology NumberField ComplexConjugate`, `open scoped Topology NumberField ComplexConjugate Classical`, `open Filter Set Topology Module`, `open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace`, `open MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Filter`, `open scoped Matrix Topology Classical ENNReal NNReal ProbabilityTheory`, `open scoped Matrix Topology Classical ENNReal`, `open scoped Topology ENNReal`, `open scoped Matrix Topology ENNReal ProbabilityTheory`, `open scoped Topology ENNReal CompactlySupported`, `open MeasureTheory Set Filter TopologicalSpace`, `open Module Set Matrix MeasureTheory Filter`, `open scoped NumberField`, `open CategoryTheory Module`, `open MeasureTheory Module Set Filter`, `open scoped BigOperators ENNReal RealInnerProductSpace`, `open Module Matrix`, `open scoped NumberField BigOperators`, `open Module MeasureTheory Set WithLp`, `open scoped NumberField BigOperators ENNReal`, `open ThetaConstruction`):
--
--   ```lean
--   theorem completedThetaXi_eq_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
--       [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
--       (hn : finrank ℚ K = d+1)  {s : ℂ} (hs : 1 < s.re) :
--       completedThetaXi σ hn s = totallyRealCompletedXi K s
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi` (definitions bundle `OAIQ244Duke011` of this split); `OAI.PrimeDegreePackets.totallyRealCompletedXi` (definitions bundle `OAIQ244Duke024` of this split); `OAI.PrimeDegreePackets.OrderedEmbeddings` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proofs of `OAI.DukePrimeDegree.completedXiGap_of_exceptionalRealZeroExclusion`, `OAI.DukePrimeDegree.cyclic_subfield_order_of_unique_character`, `OAI.DukePrimeDegree.exceptionalRealZeroExclusion_of_ray_realizations`, `OAI.DukePrimeDegree.exists_real_character_of_simple_zeta`, `OAI.DukePrimeDegree.extension_multiplicity_pos_of_ray_realizations`, `OAI.DukePrimeDegree.fixedFieldMultiplicity_le_extension`, `OAI.DukePrimeDegree.logRegularized_deriv_bound_of_completedXi_gap`, `OAI.DukePrimeDegree.no_odd_index_positive_zero_of_cyclic_characters`, `OAI.DukePrimeDegree.no_odd_index_zero_sign`, `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional`, `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, `OAI.PrimeDegreePackets.HeckeMellin.boundedDegree_near_one_zero_real_simple_unique`, `OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_logDeriv_base_le_totallyReal` and `OAI.PrimeDegreePackets.HeckeMellin.dedekindXi_realZeroPole_nonneg_totallyReal` of this split import it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/RealMellin.lean (declaration OAI.PrimeDegreePackets.HeckeMellin.completedThetaXi_eq_totallyReal)

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke024

section

attribute [-instance] _root_.QuotientGroup.Subgroup.Normal.connectedComponentOfOne _root_.RamificationTheory.Field.absoluteGaloisGroup.absoluteGaloisGroupMulSemiringActionAlgebraicClosure _root_.RamificationTheory.Field.absoluteGaloisGroup.fixingSubgroup_normal_of_normal _root_.RamificationTheory.Field.absoluteGaloisGroup.normal_fieldRangeOfExtension _root_.RamificationTheory.HilbertRamification.ValuationSubring.decompositionResidueField.instField _root_.RamificationTheory.HilbertRamification.ValuationSubring.selectedResidueField.instAlgebra _root_.RelativeIdeleGroup.baseAdeleRingNontrivial _root_.ValuationTheory.ValuationSubring.charP _root_.LocalClassFieldTheory.absoluteGaloisGroupT2 _root_.LocalClassFieldTheory.finiteFieldRingCharPrime _root_.LocalClassFieldTheory.finiteResidueBaseRingCharPrime _root_.LocalClassFieldTheory.residueAlgebraicClosureGaloisT2 _root_.LocalClassFieldTheory.residueAlgebraicClosureIsAlgClosure _root_.LocalClassFieldTheory.residueAlgebraicClosureIsGalois _root_.AlgebraicNumberTheory.Valuations.finiteWithAbsAlgebraIsAlgebraic _root_.infiniteAdeleRingT2Space _root_.relativeAdeleRingIntermediateAlgebra _root_.relativeAdeleRingTopIntermediateAlgebra
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

namespace PrimeDegreePackets.HeckeMellin
open ThetaConstruction

theorem completedThetaXi_eq_totallyReal {d : ℕ} {K : Type*} [Field K] [NumberField K]
    [NumberField.IsTotallyReal K] (σ : OrderedEmbeddings (d+1) K)
    (hn : finrank ℚ K = d+1)  {s : ℂ} (hs : 1 < s.re) :
    completedThetaXi σ hn s = totallyRealCompletedXi K s := by
  sorry

end PrimeDegreePackets.HeckeMellin

end
end

end OAI
end
