-- Prove2me | Theorems.Thm_OAI_Yau_Geometry_corrugation_actual_metric_unit_errors
-- name    : OAI.Yau.Geometry.corrugation_actual_metric_unit_errors
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:07:53.849678+00:00
-- url     : https://prove2.me/theorems/191195c7-66ba-4fda-bd43-53bae9419cec
-- title:
--   OAI.Yau.Geometry.corrugation_actual_metric_unit_errors: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Geometry.corrugation_actual_metric_unit_errors` of [lean/OAI/Geometry/NodalSets/Elliptic/CorrugationUnitRegimeErrors.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Elliptic/CorrugationUnitRegimeErrors.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Geometry`, with `open Yau.Jets Set`, `open scoped ContDiff`):
--
--   ```lean
--   theorem corrugation_actual_metric_unit_errors
--       (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (χ : _root_.OAI.Yau.Jets.Coord → ℝ)
--       {D U : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U)
--       (hg : ContDiffOn ℝ ∞ g U) (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
--       (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
--       (hχrange : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) {A : ℝ} (hA : 0 < A)
--       (hχA : ∀ z, ‖fderiv ℝ χ z‖ ≤ A*(χ z)^((7:ℝ)/8))
--       {amp : ℝ} (ha : 0 ≤ amp) (ha1 : amp ≤ 1) :
--       ∃ C : ℝ, 0 < C ∧ ∀ (s L : ℝ), 0 ≤ s → 0 < L → ∀ k : ℕ,
--         ∀ y ∈ D, ∀ x ∈ D, ∀ e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
--         (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
--         ∀ u v : _root_.OAI.Yau.Jets.Coord, g x u u = 1 → g x v v = 1 →
--         let a := frozenFrameCovector e 2
--         let b := frozenFrameCovector e 3
--         let χ₀ := χ ((corrugationScale L k)⁻¹ • (x-y))
--         let l := corrugationSlope amp (1/4)
--           (corrugationCellRadius (corrugationFastMap (corrugationFrequency k) a b (x-y)))
--         ∀ T : ℝ, 0 < T →
--         (corrugationFrequency k*χ₀*l ≤ T →
--           |corrugationMetricError g χ (corrugationPeriodicWell amp) s (corrugationFrequency k)
--             (corrugationScale L k) a b y x u v| ≤ C*s*corrugationLowErrorRate L T k) ∧
--         (T < corrugationFrequency k*χ₀*l →
--           |corrugationMetricError g χ (corrugationPeriodicWell amp) s (corrugationFrequency k)
--             (corrugationScale L k) a b y x u v| ≤
--               C*s*corrugationHighErrorRate L T k*(corrugationFrequency k*χ₀*l))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Geometry.corrugationCellRadius`, `OAI.Yau.Geometry.corrugationFastMap`, `OAI.Yau.Geometry.corrugationFrequency`, `OAI.Yau.Geometry.corrugationHighErrorRate`, `OAI.Yau.Geometry.corrugationLowErrorRate`, `OAI.Yau.Geometry.corrugationMetricError`, `OAI.Yau.Geometry.corrugationPeriodicWell`, `OAI.Yau.Geometry.corrugationScale`, `OAI.Yau.Geometry.corrugationSlope`, `OAI.Yau.Geometry.frozenFrameCovector` and `OAI.Yau.Jets.Coord` (definitions bundle `OAIQ237Ny000` of this split).
--
--   **Used by.** The proofs of `OAI.Yau.Geometry.corrugation_actual_high_admissibility` and `OAI.Yau.Geometry.corrugation_grid_admissibility` of this split import it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Elliptic/CorrugationUnitRegimeErrors.lean (declaration OAI.Yau.Geometry.corrugation_actual_metric_unit_errors)

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
import Definitions.Def_OAIQ237Ny000

section

attribute [-instance] _root_.OAI.Yau.Geometry.CompactFrameCover.instCompactSpaceParameter _root_.OAI.Yau.Geometry.CompactFrameCover.instTopologicalSpaceParameter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Geometry
open Yau.Jets Set
open scoped ContDiff
noncomputable section

theorem corrugation_actual_metric_unit_errors
    (g : _root_.OAI.Yau.Jets.Coord → _root_.OAI.Yau.Jets.Coord →L[ℝ] _root_.OAI.Yau.Jets.Coord →L[ℝ] ℝ) (χ : _root_.OAI.Yau.Jets.Coord → ℝ)
    {D U : Set _root_.OAI.Yau.Jets.Coord} (hD : IsCompact D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hg : ContDiffOn ℝ ∞ g U) (hp : ∀ y ∈ U, ∀ v, v ≠ 0 → 0 < g y v v)
    (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hχrange : ∀ z, 0 ≤ χ z ∧ χ z ≤ 1) {A : ℝ} (hA : 0 < A)
    (hχA : ∀ z, ‖fderiv ℝ χ z‖ ≤ A*(χ z)^((7:ℝ)/8))
    {amp : ℝ} (ha : 0 ≤ amp) (ha1 : amp ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s L : ℝ), 0 ≤ s → 0 < L → ∀ k : ℕ,
      ∀ y ∈ D, ∀ x ∈ D, ∀ e : _root_.OAI.Yau.Jets.Coord ≃L[ℝ] _root_.OAI.Yau.Jets.Coord,
      (∀ i j, g y (e (Pi.single i 1)) (e (Pi.single j 1)) = if i=j then 1 else 0) →
      ∀ u v : _root_.OAI.Yau.Jets.Coord, g x u u = 1 → g x v v = 1 →
      let a := frozenFrameCovector e 2
      let b := frozenFrameCovector e 3
      let χ₀ := χ ((corrugationScale L k)⁻¹ • (x-y))
      let l := corrugationSlope amp (1/4)
        (corrugationCellRadius (corrugationFastMap (corrugationFrequency k) a b (x-y)))
      ∀ T : ℝ, 0 < T →
      (corrugationFrequency k*χ₀*l ≤ T →
        |corrugationMetricError g χ (corrugationPeriodicWell amp) s (corrugationFrequency k)
          (corrugationScale L k) a b y x u v| ≤ C*s*corrugationLowErrorRate L T k) ∧
      (T < corrugationFrequency k*χ₀*l →
        |corrugationMetricError g χ (corrugationPeriodicWell amp) s (corrugationFrequency k)
          (corrugationScale L k) a b y x u v| ≤
            C*s*corrugationHighErrorRate L T k*(corrugationFrequency k*χ₀*l)) := by
  sorry

end
end Yau.Geometry

end OAI
end
