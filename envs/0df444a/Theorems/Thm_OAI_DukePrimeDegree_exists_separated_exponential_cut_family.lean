-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_exists_separated_exponential_cut_family
-- name    : OAI.DukePrimeDegree.exists_separated_exponential_cut_family
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:35:18.91409+00:00
-- url     : https://prove2.me/theorems/efbe5cbf-8d07-4351-bad9-48f306d65a40
-- title:
--   OAI.DukePrimeDegree.exists_separated_exponential_cut_family: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.exists_separated_exponential_cut_family` of [lean/OAI/NumberTheory/DukePrimeDegree/Geometry/SeparatedCutFamily.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Geometry/SeparatedCutFamily.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open MeasureTheory Set`, `open scoped ENNReal`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem exists_separated_exponential_cut_family {n : ℕ} (hn : 0 < n)
--       (μ : Measure (X n)) [IsProbabilityMeasure μ]
--       {A B R₀ a : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hR₀ : 0 ≤ R₀)
--       (ha : 0 < a) (ha1 : a ≤ 1) :
--       let r := fun m : ℕ => a*Real.exp (-B*(m:ℝ))
--       let τ := fun m => Real.log (1+r m)
--       ∃ (N : ℕ → ℕ) (z : ∀ m, Fin (N m) → X n) (c : ∀ m, Fin (N m) → ℝ)
--         (K C : ℝ), 0 < K ∧ 0 ≤ C ∧ ∀ m,
--         ((N m:ℝ≥0∞)*ENNReal.ofReal (48/τ m) ≤
--           ENNReal.ofReal (K*Real.exp (C*(m:ℝ)))) ∧
--         (∀ i j, i ≠ j → τ m/8 < quotientLogDistance (z m i) (z m j)) ∧
--         (∀ i, τ m/3 < c m i ∧ c m i < τ m/2 ∧
--           μ {x | quotientLogDistance (z m i) x=c m i}=0 ∧
--           ∀ k : ℕ, μ (realBoundaryStrip (quotientLogDistance (z m i)) (c m i) ((1/4:ℝ)^k)) ≤
--             ENNReal.ofReal (48/τ m*(1/2:ℝ)^k)) ∧
--         (∀ x, quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ A*(m:ℝ)+R₀ →
--           ∃ i, quotientLogDistance (z m i) x < c m i) ∧
--         ∀ i, ∀ x, quotientLogDistance (z m i) x < c m i →
--           ∀ y, quotientLogDistance (z m i) y < c m i →
--           ∃ g ∈ matrixBall n (r m), rightAction x g=y
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.matrixBall` (definitions bundle `OAIQ244Duke011` of this split); `OAI.DukePrimeDegree.realBoundaryStrip` (definitions bundle `OAIQ244Duke012` of this split); `OAI.DukePrimeDegree.quotientLogDistance` (definitions bundle `OAIQ244Duke023` of this split); `OAI.PrimeDegreePackets.G`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.integralGroup`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.exists_branching_cover_future_observation` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Geometry/SeparatedCutFamily.lean (declaration OAI.DukePrimeDegree.exists_separated_exponential_cut_family)

import Mathlib
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Set.Pairwise.Basic
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Probability.Kernel.Disintegration.StandardBorel
import Mathlib.Probability.Kernel.MeasurableIntegral
import Mathlib.RingTheory.Polynomial.RationalRoot
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.MulAction
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Topology.Compactness.Lindelof
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.UniformConvergence
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_DukePrimeDegree
import Definitions.Def_OAIQ244Duke023

section

attribute [-instance] _root_.OAI.DukePrimeDegree.instFiniteDimensionalRatSubtypeForallFinRealMemSubmoduleRationalRowSpace _root_.OAI.DukePrimeDegree.instFintypeCyclicSubgroups _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction _root_.OAI.DukePrimeDegree.latticeSubgroupInverseAction_continuous _root_.ValuationTheory.DiscreteValuationField.DVF.residueField.field _root_.ValuationTheory.DiscreteValuationField.DVF.valuationSubring.commRing _root_.AbsoluteValue.ostrowski_withAbsCharZero _root_.AbsoluteValue.withAbsAlgebra_isAlgebraic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_separated_exponential_cut_family {n : ℕ} (hn : 0 < n)
    (μ : Measure (X n)) [IsProbabilityMeasure μ]
    {A B R₀ a : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hR₀ : 0 ≤ R₀)
    (ha : 0 < a) (ha1 : a ≤ 1) :
    let r := fun m : ℕ => a*Real.exp (-B*(m:ℝ))
    let τ := fun m => Real.log (1+r m)
    ∃ (N : ℕ → ℕ) (z : ∀ m, Fin (N m) → X n) (c : ∀ m, Fin (N m) → ℝ)
      (K C : ℝ), 0 < K ∧ 0 ≤ C ∧ ∀ m,
      ((N m:ℝ≥0∞)*ENNReal.ofReal (48/τ m) ≤
        ENNReal.ofReal (K*Real.exp (C*(m:ℝ)))) ∧
      (∀ i j, i ≠ j → τ m/8 < quotientLogDistance (z m i) (z m j)) ∧
      (∀ i, τ m/3 < c m i ∧ c m i < τ m/2 ∧
        μ {x | quotientLogDistance (z m i) x=c m i}=0 ∧
        ∀ k : ℕ, μ (realBoundaryStrip (quotientLogDistance (z m i)) (c m i) ((1/4:ℝ)^k)) ≤
          ENNReal.ofReal (48/τ m*(1/2:ℝ)^k)) ∧
      (∀ x, quotientLogDistance (Quotient.mk _ (1 : G n)) x ≤ A*(m:ℝ)+R₀ →
        ∃ i, quotientLogDistance (z m i) x < c m i) ∧
      ∀ i, ∀ x, quotientLogDistance (z m i) x < c m i →
        ∀ y, quotientLogDistance (z m i) y < c m i →
        ∃ g ∈ matrixBall n (r m), rightAction x g=y := by
  sorry

end DukePrimeDegree

end

end OAI
end
