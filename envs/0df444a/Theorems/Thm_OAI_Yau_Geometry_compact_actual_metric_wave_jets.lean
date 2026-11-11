-- Prove2me | Theorems.Thm_OAI_Yau_Geometry_compact_actual_metric_wave_jets
-- name    : OAI.Yau.Geometry.compact_actual_metric_wave_jets
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:07:22.648561+00:00
-- url     : https://prove2.me/theorems/d07c91ff-a0c3-42e4-86ec-4d96172ab450
-- title:
--   OAI.Yau.Geometry.compact_actual_metric_wave_jets: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Geometry.compact_actual_metric_wave_jets` of [lean/OAI/Geometry/NodalSets/Coefficients/MetricWaveJets.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Coefficients/MetricWaveJets.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Geometry`, with `open Filter Set MvPolynomial`, `open scoped ContDiff Topology`, `open Yau.Jets`):
--
--   ```lean
--   theorem compact_actual_metric_wave_jets
--       (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
--       (hs : ∀ x u v, g x u v = g x v u) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
--       (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w) (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S)
--       (y : T → _root_.OAI.Yau.Jets.Coord) (hy : Continuous y) (e : T → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
--       (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
--       (ho : ∀ t i j, g (y t) (e t (Pi.single i 1)) (e t (Pi.single j 1)) = if i=j then 1 else 0)
--       {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U) (hyU : ∀ t, y t ∈ U) (hwpos : ∀ x ∈ U, 0 < w x)
--       (q : T → _root_.OAI.Yau.Jets.Coord) (a bb : T → ℝ) (ha : Continuous a) (hbb : Continuous bb)
--       (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, bb t ≠ 0) (hlen : ∀ t, bb t^2 = a t^2+4)
--       (hap : ∀ t, a t • e t (Pi.single 0 1) = metricGradient g S (y t))
--       (hbq : ∀ t, bb t • e t (Pi.single 1 1) = q t)
--       (hstrict : ∀ t, 0 < sourceHessian g S (y t) (metricGradient g S (y t)) (metricGradient g S (y t)) +
--         sourceHessian g S (y t) (q t) (q t)) (m J : ℕ) (hm : 1 ≤ m) :
--       ∃ (beta : ContDiffBump (0:_root_.OAI.Yau.Jets.Coord)) (phi : T → CPoly) (A : ℕ → T → CPoly),
--         NormalOperatorFamily (extendedPrincipal g y e beta) (extendedDrift g w y e beta) ∧
--         MetricWaveJetFamily (extendedPrincipal g y e beta) (extendedDrift g w y e beta)
--           (fun t ↦ S (y t)) a bb
--           (fun t ↦ envelopeHessian (S ∘ actualMetricChart g (y t) (e t))) m J phi A ∧
--         ∃ c > 0, ∀ᶠ N : ℝ in atTop, ∀ t, ∀ x : _root_.OAI.Yau.Jets.Coord, ‖x‖ ≤ 2*N^(-1/3:ℝ) →
--           (reval (phi t) x).re-S (actualMetricChart g (y t) (e t) x) ≤ -c*‖x‖^2
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Geometry.MetricWaveJetFamily`, `OAI.Yau.Geometry.NormalOperatorFamily`, `OAI.Yau.Geometry.actualMetricChart`, `OAI.Yau.Geometry.clmModule`, `OAI.Yau.Geometry.clmTopology`, `OAI.Yau.Geometry.extendedDrift`, `OAI.Yau.Geometry.extendedPrincipal`, `OAI.Yau.Geometry.metricGradient`, `OAI.Yau.Geometry.sourceHessian`, `OAI.Yau.Jets.CPoly`, `OAI.Yau.Jets.Coord`, `OAI.Yau.Jets.envelopeHessian` and `OAI.Yau.Jets.reval` (definitions bundle `OAIQ237Ny000` of this split).
--
--   **Used by.** The proof of `OAI.Yau.Geometry.constructed_coordinate_wave_estimates` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Coefficients/MetricWaveJets.lean (declaration OAI.Yau.Geometry.compact_actual_metric_wave_jets)

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
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
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_OAIQ237Ny000

section

attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Filter Set MvPolynomial
open scoped ContDiff Topology
open Yau.Jets
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem compact_actual_metric_wave_jets
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (hg : ContDiff ℝ ∞ g)
    (hs : ∀ x u v, g x u v = g x v u) (hpos : ∀ x v, v ≠ 0 → 0 < g x v v)
    (w : _root_.OAI.Yau.Jets.Coord → ℝ) (hw : ContDiff ℝ ∞ w) (S : _root_.OAI.Yau.Jets.Coord → ℝ) (hS : ContDiff ℝ ∞ S)
    (y : T → _root_.OAI.Yau.Jets.Coord) (hy : Continuous y) (e : T → _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord)
    (he : Continuous (fun t ↦ (e t).toContinuousLinearMap))
    (ho : ∀ t i j, g (y t) (e t (Pi.single i 1)) (e t (Pi.single j 1)) = if i=j then 1 else 0)
    {U : Set _root_.OAI.Yau.Jets.Coord} (hU : IsOpen U) (hyU : ∀ t, y t ∈ U) (hwpos : ∀ x ∈ U, 0 < w x)
    (q : T → _root_.OAI.Yau.Jets.Coord) (a bb : T → ℝ) (ha : Continuous a) (hbb : Continuous bb)
    (ha0 : ∀ t, a t ≠ 0) (hb0 : ∀ t, bb t ≠ 0) (hlen : ∀ t, bb t^2 = a t^2+4)
    (hap : ∀ t, a t • e t (Pi.single 0 1) = metricGradient g S (y t))
    (hbq : ∀ t, bb t • e t (Pi.single 1 1) = q t)
    (hstrict : ∀ t, 0 < sourceHessian g S (y t) (metricGradient g S (y t)) (metricGradient g S (y t)) +
      sourceHessian g S (y t) (q t) (q t)) (m J : ℕ) (hm : 1 ≤ m) :
    ∃ (beta : ContDiffBump (0:_root_.OAI.Yau.Jets.Coord)) (phi : T → CPoly) (A : ℕ → T → CPoly),
      NormalOperatorFamily (extendedPrincipal g y e beta) (extendedDrift g w y e beta) ∧
      MetricWaveJetFamily (extendedPrincipal g y e beta) (extendedDrift g w y e beta)
        (fun t ↦ S (y t)) a bb
        (fun t ↦ envelopeHessian (S ∘ actualMetricChart g (y t) (e t))) m J phi A ∧
      ∃ c > 0, ∀ᶠ N : ℝ in atTop, ∀ t, ∀ x : _root_.OAI.Yau.Jets.Coord, ‖x‖ ≤ 2*N^(-1/3:ℝ) →
        (reval (phi t) x).re-S (actualMetricChart g (y t) (e t) x) ≤ -c*‖x‖^2 := by
  sorry

end
end Yau.Geometry

end OAI
end
