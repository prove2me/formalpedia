-- Prove2me | Theorems.Thm_OAI_Yau_Geometry_corrugation_projected_direction_freezing
-- name    : OAI.Yau.Geometry.corrugation_projected_direction_freezing
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:27:12.635846+00:00
-- url     : https://prove2.me/theorems/9ae8bb3d-2e72-452b-a6e5-1070fee1b885
-- title:
--   OAI.Yau.Geometry.corrugation_projected_direction_freezing: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Geometry.corrugation_projected_direction_freezing` of [lean/OAI/Geometry/NodalSets/Elliptic/CorrugationProjectedDirections.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Elliptic/CorrugationProjectedDirections.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Geometry`, with `open Yau.Jets Set Filter`, `open scoped ContDiff Topology`):
--
--   ```lean
--   theorem corrugation_projected_direction_freezing
--       (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ)
--       {D U : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hconv : Convex ℝ D)
--       (hU : IsOpen U) (hDU : D ⊆ U)
--       (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
--       (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
--       (hn : ∀ y ∈ D, metricGradient g S y ≠ 0)
--       (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
--       (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
--       {amp L : ℝ} (ha : 0 ≤ amp) (ha1 : amp ≤ 1) (hL : 0 < L) :
--       ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
--         ∀ y ∈ D, ∀ x ∈ D, ‖x-y‖ ≤ corrugationScale L k →
--         ∀ e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
--         e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
--         (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
--         let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
--           (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
--           (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
--         let w := corrugationLeadingVector amp (χ ((corrugationScale L k)⁻¹ • (x-y))) e
--           (corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y))
--         ∀ t : _root_.OAI.Yau.Jets.Coord, g y t t = 1 → g y w t = 0 →
--         let q := metricPerpProjection (g x) (metricNormalize (g x) p) t
--         q ≠ 0 ∧ g x (metricNormalize (g x) q) (metricNormalize (g x) q) = 1 ∧
--           g x (metricNormalize (g x) p) (metricNormalize (g x) q) = 0 ∧
--           ‖metricNormalize (g x) q-t‖ ≤ C*corrugationGradientRate L k
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Geometry.corrugationFastMap`, `OAI.Yau.Geometry.corrugationFrequency`, `OAI.Yau.Geometry.corrugationGradientRate`, `OAI.Yau.Geometry.corrugationLeadingVector`, `OAI.Yau.Geometry.corrugationOldSlope`, `OAI.Yau.Geometry.corrugationPeriodicWell`, `OAI.Yau.Geometry.corrugationScale`, `OAI.Yau.Geometry.frozenFrameCovector`, `OAI.Yau.Geometry.localizedCorrugation`, `OAI.Yau.Geometry.metricGradient`, `OAI.Yau.Geometry.metricNormalize` and `OAI.Yau.Jets.Coord` (definitions bundle `OAIQ237Ny000` of this split); `OAI.Yau.Geometry.metricPerpProjection` (definitions bundle `OAIQ237Ny002` of this split).
--
--   **Used by.** The proofs of `OAI.Yau.Geometry.corrugation_actual_angular_estimates`, `OAI.Yau.Geometry.corrugation_actual_low_old_margin` and `OAI.Yau.Geometry.corrugation_actual_low_radial` of this split import it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Elliptic/CorrugationProjectedDirections.lean (declaration OAI.Yau.Geometry.corrugation_projected_direction_freezing)

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
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
import Mathlib.Topology.Order.Compact
import Definitions.Def_OAIQ237Ny002

section

attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set Filter
open scoped ContDiff Topology
noncomputable section

theorem corrugation_projected_direction_freezing
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (S χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    {D U : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hconv : Convex ℝ D)
    (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hS : ContDiffOn ℝ ∞ S U)
    (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hn : ∀ y ∈ D, metricGradient g S y ≠ 0)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    {amp L : ℝ} (ha : 0 ≤ amp) (ha1 : amp ≤ 1) (hL : 0 < L) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop,
      ∀ y ∈ D, ∀ x ∈ D, ‖x-y‖ ≤ corrugationScale L k →
      ∀ e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      e (Pi.single 0 1) = (corrugationOldSlope g S y)⁻¹ • metricGradient g S y →
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      let p := metricGradient g (S+localizedCorrugation χ (corrugationPeriodicWell amp)
        (corrugationOldSlope g S y) (corrugationFrequency k) (corrugationScale L k)
        (frozenFrameCovector e 2) (frozenFrameCovector e 3) y) x
      let w := corrugationLeadingVector amp (χ ((corrugationScale L k)⁻¹ • (x-y))) e
        (corrugationFastMap (corrugationFrequency k) (frozenFrameCovector e 2) (frozenFrameCovector e 3) (x-y))
      ∀ t : _root_.OAI.Yau.Jets.Coord, g y t t = 1 → g y w t = 0 →
      let q := metricPerpProjection (g x) (metricNormalize (g x) p) t
      q ≠ 0 ∧ g x (metricNormalize (g x) q) (metricNormalize (g x) q) = 1 ∧
        g x (metricNormalize (g x) p) (metricNormalize (g x) q) = 0 ∧
        ‖metricNormalize (g x) q-t‖ ≤ C*corrugationGradientRate L k := by
  sorry

end
end Yau.Geometry

end OAI
end
