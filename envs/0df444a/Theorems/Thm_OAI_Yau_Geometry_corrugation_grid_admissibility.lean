-- Prove2me | Theorems.Thm_OAI_Yau_Geometry_corrugation_grid_admissibility
-- name    : OAI.Yau.Geometry.corrugation_grid_admissibility
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:07:35.556897+00:00
-- url     : https://prove2.me/theorems/6de9464c-9284-42fa-81fa-c6648d14e76f
-- title:
--   OAI.Yau.Geometry.corrugation_grid_admissibility: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Geometry.corrugation_grid_admissibility` of [lean/OAI/Geometry/NodalSets/Elliptic/CorrugationGridAdmissibility.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Elliptic/CorrugationGridAdmissibility.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Geometry`, with `open Yau.Jets Set Filter Metric`, `open scoped ContDiff Topology`):
--
--   ```lean
--   theorem corrugation_grid_admissibility (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
--       (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ)
--       {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U) (hDU : Icc o (fun i ↦ o i+L) ⊆ U)
--       (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
--       (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
--       (hsym : ∀ y ∈ Icc o (fun i ↦ o i+L), ∀ u v, g y u v = g y v u)
--       (hadm : ∀ y ∈ Icc o (fun i ↦ o i+L), metricGradient g S y ≠ 0 ∧
--         ∃ q : _root_.OAI.Yau.Jets.Coord, g y q q = 1 ∧ g y (metricGradient g S y) q = 0 ∧
--           0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
--             (g y (metricGradient g S y) (metricGradient g S y)+4)*sourceHessian g S y q q)
--       (hχ : ContDiff ℝ ∞ χ) (hχsupp : tsupport χ ⊆ ball (0:_root_.OAI.Yau.Jets.Coord) (1/2))
--       (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
--       {Aχ : ℝ} (hAχ : 0 < Aχ) (hχA : ∀ z, ‖fderiv ℝ χ z‖ ≤ Aχ*(χ z)^((7:ℝ)/8)) :
--       ∀ᶠ k : ℕ in atTop,
--         ∀ e : (Fin 4 → Fin (corrugationSubdivision k)) → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
--         (∀ i, e i (Pi.single 0 1) =
--           (corrugationOldSlope g S (corrugationCubeCenter o L (corrugationSubdivision k) i))⁻¹ •
--             metricGradient g S (corrugationCubeCenter o L (corrugationSubdivision k) i)) →
--         (∀ i a b, g (corrugationCubeCenter o L (corrugationSubdivision k) i)
--           (e i (Pi.single a 1)) (e i (Pi.single b 1)) = if a=b then 1 else 0) →
--         (∀ i, let y := corrugationCubeCenter o L (corrugationSubdivision k) i
--           ∀ v, g y v v = 1 → g y (metricGradient g S y) v = 0 →
--             sourceHessian g S y v v ≤ sourceHessian g S y (e i (Pi.single 1 1)) (e i (Pi.single 1 1))) →
--         ∀ x ∈ Icc o (fun i ↦ o i+L),
--           let W := corrugationEnvelopePerturbation o L k g S χ corrugationFixedAmplitude e
--           let p := metricGradient g (S+W) x
--           p ≠ 0 ∧ ∃ t : _root_.OAI.Yau.Jets.Coord, g x t t = 1 ∧ g x p t = 0 ∧
--             0 < sourceHessian g (S+W) x p p+(g x p p+4)*sourceHessian g (S+W) x t t
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Geometry.clmModule`, `OAI.Yau.Geometry.clmTopology`, `OAI.Yau.Geometry.corrugationCubeCenter`, `OAI.Yau.Geometry.corrugationEnvelopePerturbation`, `OAI.Yau.Geometry.corrugationFixedAmplitude`, `OAI.Yau.Geometry.corrugationOldSlope`, `OAI.Yau.Geometry.corrugationSubdivision`, `OAI.Yau.Geometry.metricGradient`, `OAI.Yau.Geometry.sourceHessian` and `OAI.Yau.Jets.Coord` (definitions bundle `OAIQ237Ny000` of this split).
--
--   **Used by.** The proof of `OAI.Yau.Geometry.exists_placed_envelope` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Elliptic/CorrugationGridAdmissibility.lean (declaration OAI.Yau.Geometry.corrugation_grid_admissibility)

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Abs
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
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
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
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_OAIQ237Ny000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter Metric
open scoped ContDiff Topology
noncomputable section

theorem corrugation_grid_admissibility (o : _root_.OAI.Yau.Jets.Coord) {L : ℝ} (hL : 0 < L)
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U) (hDU : Icc o (fun i ↦ o i+L) ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hsym : ∀ y ∈ Icc o (fun i ↦ o i+L), ∀ u v, g y u v = g y v u)
    (hadm : ∀ y ∈ Icc o (fun i ↦ o i+L), metricGradient g S y ≠ 0 ∧
      ∃ q : _root_.OAI.Yau.Jets.Coord, g y q q = 1 ∧ g y (metricGradient g S y) q = 0 ∧
        0 < sourceHessian g S y (metricGradient g S y) (metricGradient g S y) +
          (g y (metricGradient g S y) (metricGradient g S y)+4)*sourceHessian g S y q q)
    (hχ : ContDiff ℝ ∞ χ) (hχsupp : tsupport χ ⊆ ball (0:_root_.OAI.Yau.Jets.Coord) (1/2))
    (hχ0 : ∀ z, 0 ≤ χ z) (hχ1 : ∀ z, χ z ≤ 1)
    {Aχ : ℝ} (hAχ : 0 < Aχ) (hχA : ∀ z, ‖fderiv ℝ χ z‖ ≤ Aχ*(χ z)^((7:ℝ)/8)) :
    ∀ᶠ k : ℕ in atTop,
      ∀ e : (Fin 4 → Fin (corrugationSubdivision k)) → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      (∀ i, e i (Pi.single 0 1) =
        (corrugationOldSlope g S (corrugationCubeCenter o L (corrugationSubdivision k) i))⁻¹ •
          metricGradient g S (corrugationCubeCenter o L (corrugationSubdivision k) i)) →
      (∀ i a b, g (corrugationCubeCenter o L (corrugationSubdivision k) i)
        (e i (Pi.single a 1)) (e i (Pi.single b 1)) = if a=b then 1 else 0) →
      (∀ i, let y := corrugationCubeCenter o L (corrugationSubdivision k) i
        ∀ v, g y v v = 1 → g y (metricGradient g S y) v = 0 →
          sourceHessian g S y v v ≤ sourceHessian g S y (e i (Pi.single 1 1)) (e i (Pi.single 1 1))) →
      ∀ x ∈ Icc o (fun i ↦ o i+L),
        let W := corrugationEnvelopePerturbation o L k g S χ corrugationFixedAmplitude e
        let p := metricGradient g (S+W) x
        p ≠ 0 ∧ ∃ t : _root_.OAI.Yau.Jets.Coord, g x t t = 1 ∧ g x p t = 0 ∧
          0 < sourceHessian g (S+W) x p p+(g x p p+4)*sourceHessian g (S+W) x t t := by
  sorry

end
end Yau.Geometry

end OAI
end
