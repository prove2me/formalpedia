-- Prove2me | Theorems.Thm_OAI_Yau_Geometry_corrugation_grid_integrated_gain
-- name    : OAI.Yau.Geometry.corrugation_grid_integrated_gain
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:07:55.965098+00:00
-- url     : https://prove2.me/theorems/25a86edd-2905-46b6-bac0-4bed47710b94
-- title:
--   OAI.Yau.Geometry.corrugation_grid_integrated_gain: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Geometry.corrugation_grid_integrated_gain` of [lean/OAI/Geometry/NodalSets/Elliptic/CorrugationGridGain.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Elliptic/CorrugationGridGain.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Geometry`, with `open Yau.Jets Set Filter Metric MeasureTheory`, `open scoped ContDiff Topology`):
--
--   ```lean
--   theorem corrugation_grid_integrated_gain {c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
--       ∃ γ : ℝ, 0 < γ ∧ ∀ (o : _root_.OAI.Yau.Jets.Coord) (L : ℝ), 0 < L →
--         ∀ (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
--         (U : Set _root_.OAI.Yau.Jets.Coord), IsOpen U → Icc o (fun j ↦ o j+L) ⊆ U →
--         ContDiffOn ℝ ∞ g U → ContDiffOn ℝ ∞ S U →
--         (∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v) →
--         (∀ y ∈ Icc o (fun j ↦ o j+L), metricGradient g S y ≠ 0) →
--         (∀ y ∈ Icc o (fun j ↦ o j+L), ‖g y‖ ≤ M ∧ ∀ v, c*‖v‖^2 ≤ g y v v) →
--         ∀ᶠ k : ℕ in atTop,
--         ∀ e : (Fin 4 → Fin (corrugationSubdivision k)) → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
--         (∀ i, let y := corrugationCubeCenter o L (corrugationSubdivision k) i
--           e i (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y ∧
--           (∀ a b, g y (e i (Pi.single a 1)) (e i (Pi.single b 1)) = if a=b then 1 else 0)) →
--         (1+γ)*(∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g S x) ≤
--           ∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g
--             (S+corrugationEnvelopePerturbation o L k g S corrugationFixedCutoff corrugationFixedAmplitude e) x
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Geometry.corrugationCubeCenter`, `OAI.Yau.Geometry.corrugationEnvelopePerturbation`, `OAI.Yau.Geometry.corrugationFixedAmplitude`, `OAI.Yau.Geometry.corrugationFixedCutoff`, `OAI.Yau.Geometry.corrugationOldSlope`, `OAI.Yau.Geometry.corrugationSubdivision`, `OAI.Yau.Geometry.metricGradient` and `OAI.Yau.Jets.Coord` (definitions bundle `OAIQ237Ny000` of this split).
--
--   **Used by.** The proof of `OAI.Yau.Geometry.exists_placed_envelope` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Elliptic/CorrugationGridGain.lean (declaration OAI.Yau.Geometry.corrugation_grid_integrated_gain)

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Matrix.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Definitions.Def_OAIQ237Ny000

section

attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric MeasureTheory
open scoped ContDiff Topology
noncomputable section

theorem corrugation_grid_integrated_gain {c M : ℝ} (hc : 0 < c) (hM : 0 < M) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ (o : _root_.OAI.Yau.Jets.Coord) (L : ℝ), 0 < L →
      ∀ (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S : _root_.OAI.Yau.Jets.Coord → ℝ)
      (U : Set _root_.OAI.Yau.Jets.Coord), IsOpen U → Icc o (fun j ↦ o j+L) ⊆ U →
      ContDiffOn ℝ ∞ g U → ContDiffOn ℝ ∞ S U →
      (∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v) →
      (∀ y ∈ Icc o (fun j ↦ o j+L), metricGradient g S y ≠ 0) →
      (∀ y ∈ Icc o (fun j ↦ o j+L), ‖g y‖ ≤ M ∧ ∀ v, c*‖v‖^2 ≤ g y v v) →
      ∀ᶠ k : ℕ in atTop,
      ∀ e : (Fin 4 → Fin (corrugationSubdivision k)) → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      (∀ i, let y := corrugationCubeCenter o L (corrugationSubdivision k) i
        e i (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y ∧
        (∀ a b, g y (e i (Pi.single a 1)) (e i (Pi.single b 1)) = if a=b then 1 else 0)) →
      (1+γ)*(∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g S x) ≤
        ∫ x in Icc o (fun j ↦ o j+L), corrugationOldSlope g
          (S+corrugationEnvelopePerturbation o L k g S corrugationFixedCutoff corrugationFixedAmplitude e) x := by
  sorry

end
end Yau.Geometry

end OAI
end
