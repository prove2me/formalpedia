-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_exists_singleBlock_terminal_generic_set
-- name    : OAI.DukePrimeDegree.exists_singleBlock_terminal_generic_set
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:38:18.614224+00:00
-- url     : https://prove2.me/theorems/b0927a7a-1cdb-4e78-831b-a551a4dd9de9
-- title:
--   OAI.DukePrimeDegree.exists_singleBlock_terminal_generic_set: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.exists_singleBlock_terminal_generic_set` of [lean/OAI/NumberTheory/DukePrimeDegree/Dynamics/SingleBlockGenericSet.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Dynamics/SingleBlockGenericSet.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open MeasureTheory Set Filter`, `open scoped Topology ENNReal BoundedContinuousFunction`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem exists_singleBlock_terminal_generic_set {n : ℕ}
--       (S : Set (Fin n)) (μ : Measure (X n)) [IsProbabilityMeasure μ]
--       [ErgodicSMul (singleBlockRootGroup S) (X n) μ]
--       (F : Finset (CompactlySupportedContinuousMap (X n) ℝ))
--       (K : Set (G n)) (hK : IsCompact K)
--       (ε δ η : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η) :
--       ∃ E : Set (X n), MeasurableSet E ∧ μ Eᶜ ≤ ENNReal.ofReal η ∧
--         ∃ R : ℝ, 0 < R ∧
--           ∀ x ∈ E, ∀ i ∈ S, ∀ j ∈ S, ∀ (hij : i ≠ j), ∀ f ∈ F, ∀ T ≥ R,
--             |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T,
--               f (rightAction x (Matrix.SpecialLinearGroup.transvection hij (-t)))) -
--                 ∫ y, f y ∂μ| ≤ ε ∧
--             ∀ h ∈ K,
--               |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T,
--                 f (rightAction (rightAction x
--                   (Matrix.SpecialLinearGroup.transvection hij (-t))) h)) -
--                     ∫ y, f (rightAction y h) ∂μ| ≤ ε
--   ```
--
--   **Definitions.** The statement is written with `OAI.DukePrimeDegree.latticeSubgroupInverseAction` and `OAI.DukePrimeDegree.singleBlockRootGroup` (definitions bundle `OAIQ244Duke023` of this split); `OAI.PrimeDegreePackets.G`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.integralGroup`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.exists_positive_singleBlock_orbit` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Dynamics/SingleBlockGenericSet.lean (declaration OAI.DukePrimeDegree.exists_singleBlock_terminal_generic_set)

import Mathlib
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Mathlib.Algebra.Group.Action.End
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.InnerProductSpace.MeanErgodic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finite.Perm
import Mathlib.Data.Finset.Max
import Mathlib.Data.Matrix.Basis
import Mathlib.Data.Matrix.Block
import Mathlib.Dynamics.BirkhoffSum.Average
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.BirkhoffSum.QuasiMeasurePreserving
import Mathlib.Dynamics.Ergodic.Action.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.Function
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.RingTheory.Flat.IsBaseChange
import Mathlib.RingTheory.Localization.Module
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Compactness.SigmaCompact
import Mathlib.Topology.Connected.TotallyDisconnected
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.IsometricSMul
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke023

section

attribute [-instance] _root_.LubinTate.compatibleGroupFamiliesGroup _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.specialLinear_secondCountable _root_.OAI.DukePrimeDegree.specialLinear_standardBorel _root_.OAI.DukePrimeDegree.upperRootTransverse_secondCountable _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set Filter
open scoped Topology ENNReal BoundedContinuousFunction

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_singleBlock_terminal_generic_set {n : ℕ}
    (S : Set (Fin n)) (μ : Measure (X n)) [IsProbabilityMeasure μ]
    [ErgodicSMul (singleBlockRootGroup S) (X n) μ]
    (F : Finset (CompactlySupportedContinuousMap (X n) ℝ))
    (K : Set (G n)) (hK : IsCompact K)
    (ε δ η : ℝ) (hε : 0 < ε) (hδ : 0 < δ) (hδ1 : δ < 1) (hη : 0 < η) :
    ∃ E : Set (X n), MeasurableSet E ∧ μ Eᶜ ≤ ENNReal.ofReal η ∧
      ∃ R : ℝ, 0 < R ∧
        ∀ x ∈ E, ∀ i ∈ S, ∀ j ∈ S, ∀ (hij : i ≠ j), ∀ f ∈ F, ∀ T ≥ R,
          |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T,
            f (rightAction x (Matrix.SpecialLinearGroup.transvection hij (-t)))) -
              ∫ y, f y ∂μ| ≤ ε ∧
          ∀ h ∈ K,
            |(δ * T)⁻¹ * (∫ t in ((1 - δ) * T)..T,
              f (rightAction (rightAction x
                (Matrix.SpecialLinearGroup.transvection hij (-t))) h)) -
                  ∫ y, f (rightAction y h) ∂μ| ≤ ε := by
  sorry

end DukePrimeDegree

end

end OAI
end
