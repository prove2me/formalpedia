-- Prove2me | Theorems.Thm_OAI_PrimeDegreePackets_positive_entropy_components_ae
-- name    : OAI.PrimeDegreePackets.positive_entropy_components_ae
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:46:05.791442+00:00
-- url     : https://prove2.me/theorems/89202bef-e339-406e-abaf-00904041cfe6
-- title:
--   OAI.PrimeDegreePackets.positive_entropy_components_ae: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PrimeDegreePackets.positive_entropy_components_ae` of [lean/OAI/NumberTheory/PrimePackets/KernelEntropy.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/KernelEntropy.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PrimeDegreePackets`, with `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal`, `open MeasureTheory Filter Set Module`, `open scoped TensorProduct`, `open Set Module`, `open MeasureTheory Set`, `open scoped ENNReal`, `open IsDiscreteValuationRing IsLocalRing`, `open scoped ENNReal BigOperators`, `open MeasureTheory Set IsDiscreteValuationRing`, `open Filter`, `open scoped BigOperators Topology`, `open NumberField`, `open scoped NumberField nonZeroDivisors`, `open scoped BigOperators ArithmeticFunction.zeta`, `open Finset`, `open scoped BigOperators Classical`, `open Finset Nat ArithmeticFunction BoundingSieve`, `open scoped BigOperators Classical`, `open Finset Nat`, `open scoped BigOperators`, `open Filter Topology`, `open scoped nonZeroDivisors`, `open Ideal NumberField Finset UniqueFactorizationMonoid`, `open Filter Set Topology NumberField`, `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors`, `open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace`, `open Filter Set Topology`, `open scoped Matrix Topology BigOperators Classical TensorProduct ENNReal NumberField Pointwise nonZeroDivisors RealInnerProductSpace`, `open MeasureTheory Filter Set Module NumberField FractionalIdeal Topology TopologicalSpace Matrix`, `open MeasureTheory Filter Set Module TopologicalSpace`, `open MeasureTheory Filter Set`, `open scoped BigOperators Topology ENNReal`, `open scoped BigOperators Topology ENNReal Classical`, `open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise`, `open scoped BigOperators Topology ENNReal Classical Matrix Matrix.Norms.Elementwise Pointwise`, `open scoped BigOperators Topology ENNReal Classical Matrix Pointwise`, `open scoped BigOperators Topology ENNReal Classical Matrix`, `open MeasureTheory ProbabilityTheory Filter Set`):
--
--   ```lean
--   theorem positive_entropy_components_ae {d : ℕ} {Z : Type*} [MeasurableSpace Z]
--       (τ : Measure Z) [IsProbabilityMeasure τ]
--       (κ : Kernel Z (X (d+1))) [IsMarkovKernel κ]
--       (hball : OrdinaryBallBound (d+1) (κ ∘ₘ τ))
--       (hA : ∀ᵐ z ∂τ, ∀ u : LogCoordinates d,
--         Measure.map (fun x => rightAction x (diagonalFlow u)) (κ z) = κ z) :
--       ∀ᵐ z ∂τ, 0 < measureEntropy (κ z)
--         (fun x => rightAction x (diagonalOneParameter (regularDiagonalWeights d)
--           (regularDiagonalWeights_sum d) 1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.diagonalOneParameter`, `OAI.PrimeDegreePackets.measureEntropy`, `OAI.PrimeDegreePackets.regularDiagonalWeights` and `OAI.PrimeDegreePackets.regularDiagonalWeights_sum` (definitions bundle `OAIQ244Duke011` of this split); `OAI.PrimeDegreePackets.OrdinaryBallBound` (definitions bundle `OAIQ244Duke023` of this split); `OAI.PrimeDegreePackets.LogCoordinates`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.diagonalFlow`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.packet_limit_isHaar_of_scale_and_EKL` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/PrimePackets/KernelEntropy.lean (declaration OAI.PrimeDegreePackets.positive_entropy_components_ae)

import Mathlib
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke023

section

attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.OAI.PrimeDegreePackets.ThetaConstruction.integerTranslationAction _root_.OAI.PrimeDegreePackets.diagonalLogAction _root_.OAI.PrimeDegreePackets.instSecondCountableTopologyLeafTestSpace _root_.OAI.PrimeDegreePackets.rootGroupBorelSpace _root_.OAI.PrimeDegreePackets.rootGroupMeasurableSpace _root_.OAI.PrimeDegreePackets.rootSliceSecondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
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
open scoped BigOperators Classical
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

namespace PrimeDegreePackets

theorem positive_entropy_components_ae {d : ℕ} {Z : Type*} [MeasurableSpace Z]
    (τ : Measure Z) [IsProbabilityMeasure τ]
    (κ : Kernel Z (X (d+1))) [IsMarkovKernel κ]
    (hball : OrdinaryBallBound (d+1) (κ ∘ₘ τ))
    (hA : ∀ᵐ z ∂τ, ∀ u : LogCoordinates d,
      Measure.map (fun x => rightAction x (diagonalFlow u)) (κ z) = κ z) :
    ∀ᵐ z ∂τ, 0 < measureEntropy (κ z)
      (fun x => rightAction x (diagonalOneParameter (regularDiagonalWeights d)
        (regularDiagonalWeights_sum d) 1)) := by
  sorry

end PrimeDegreePackets

open Set Filter
open scoped Topology

open scoped Classical

open scoped Topology ENNReal Classical
end
end

end OAI
end
