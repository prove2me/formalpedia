-- Prove2me | Theorems.Thm_OAI_DukePrimeDegree_exists_noncentral_neutral_return_sequence
-- name    : OAI.DukePrimeDegree.exists_noncentral_neutral_return_sequence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-13T06:12:54.10923+00:00
-- url     : https://prove2.me/theorems/f29171d9-faf1-4435-9c55-1fe8aaf7089f
-- title:
--   OAI.DukePrimeDegree.exists_noncentral_neutral_return_sequence: intermediate lemma from OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DukePrimeDegree.prime_degree_packet_measure_equidistribution_unconditional` and `OAI.DukePrimeDegree.prime_degree_packet_measures_tendsto_haar_unconditional`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type*, OpenAI Math Release, September 24, 2026, result family 15, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DukePrimeDegree.exists_noncentral_neutral_return_sequence` of [lean/OAI/NumberTheory/DukePrimeDegree/Dynamics/NoncentralReturns.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Dynamics/NoncentralReturns.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DukePrimeDegree`, with `open Set Filter MeasureTheory`, `open scoped Topology`, `open PrimeDegreePackets`):
--
--   ```lean
--   theorem exists_noncentral_neutral_return_sequence
--       (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
--       (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
--       (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
--       (K : Set (X (d + 1))) (hK : MeasurableSet K) (hpos : μ K ≠ 0) :
--       ∃ (x y : ℕ → X (d + 1)) (g : ℕ → G (d + 1)),
--         Tendsto g atTop (𝓝 1) ∧ ∀ m,
--           x m ∈ K ∧ y m ∈ K ∧ rightAction (x m) (g m) = y m ∧
--           (¬ ∀ t : ℝ, g m * Matrix.SpecialLinearGroup.transvection hij t =
--             Matrix.SpecialLinearGroup.transvection hij t * g m) ∧
--           ∃ ell : Fin (d + 1) → ℝ, ∃ hell : ∑ a, ell a = 0,
--             ell i = ell j ∧ rightAction (x m) (diagonalOneParameter ell hell 1) = y m
--   ```
--
--   **Definitions.** The statement is written with `OAI.PrimeDegreePackets.diagonalOneParameter` (definitions bundle `OAIQ244Duke011` of this split); `OAI.PrimeDegreePackets.G`, `OAI.PrimeDegreePackets.LogCoordinates`, `OAI.PrimeDegreePackets.X`, `OAI.PrimeDegreePackets.diagonalFlow`, `OAI.PrimeDegreePackets.rightAction` and `OAI.PrimeDegreePackets.xMeasurableSpace` (the published bundle `Def_DukePrimeDegree`).
--
--   **Used by.** The proof of `OAI.DukePrimeDegree.exists_distinct_equal_leaf_horospherical_pair` of this split imports it.
-- source:
--   OpenAI, Equidistribution of Prime-Degree Torus Packets with Arbitrary Local Type, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 15; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Equidistribution-of-Prime-Degree-Torus-Packets-with-Arbitrary-Local-Type-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/NumberTheory/DukePrimeDegree/Dynamics/NoncentralReturns.lean (declaration OAI.DukePrimeDegree.exists_noncentral_neutral_return_sequence)

import Mathlib
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Dynamics.Ergodic.Conservative
import Mathlib.FieldTheory.Minpoly.IsConjRoot
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Besicovitch
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.MeasureTheory.Measure.Support
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
import Definitions.Def_OAIQ244Duke011

section

attribute [-instance] _root_.OAI.DukePrimeDegree.specialLinear_secondCountable
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open Set Filter MeasureTheory
open scoped Topology

namespace DukePrimeDegree
open PrimeDegreePackets

theorem exists_noncentral_neutral_return_sequence
    (d : ℕ) (hd : 2 < d + 1) {i j : Fin (d + 1)} (hij : i ≠ j)
    (μ : Measure (X (d + 1))) [IsProbabilityMeasure μ]
    (hA : ∀ u : LogCoordinates d, μ.map (fun x => rightAction x (diagonalFlow u)) = μ)
    (K : Set (X (d + 1))) (hK : MeasurableSet K) (hpos : μ K ≠ 0) :
    ∃ (x y : ℕ → X (d + 1)) (g : ℕ → G (d + 1)),
      Tendsto g atTop (𝓝 1) ∧ ∀ m,
        x m ∈ K ∧ y m ∈ K ∧ rightAction (x m) (g m) = y m ∧
        (¬ ∀ t : ℝ, g m * Matrix.SpecialLinearGroup.transvection hij t =
          Matrix.SpecialLinearGroup.transvection hij t * g m) ∧
        ∃ ell : Fin (d + 1) → ℝ, ∃ hell : ∑ a, ell a = 0,
          ell i = ell j ∧ rightAction (x m) (diagonalOneParameter ell hell 1) = y m := by
  sorry

end DukePrimeDegree

end

end OAI
end
