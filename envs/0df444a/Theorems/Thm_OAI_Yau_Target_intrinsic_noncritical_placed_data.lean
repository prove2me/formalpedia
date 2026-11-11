-- Prove2me | Theorems.Thm_OAI_Yau_Target_intrinsic_noncritical_placed_data
-- name    : OAI.Yau.Target.intrinsic_noncritical_placed_data
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:30:35.167284+00:00
-- url     : https://prove2.me/theorems/426f154b-7e3e-475a-99fe-1f03d93c4304
-- title:
--   OAI.Yau.Target.intrinsic_noncritical_placed_data: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Target.intrinsic_noncritical_placed_data` of [lean/OAI/Geometry/NodalSets/Elliptic/IntrinsicNoncriticalPlacement.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Elliptic/IntrinsicNoncriticalPlacement.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Target`, with `open Manifold Yau.Geometry Yau.Jets Set Metric`, `open scoped ContDiff`):
--
--   ```lean
--   theorem intrinsic_noncritical_placed_data : ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
--       seedCoordCube a ⊆ seedCoordPatch r ∧ closure (seedCoordPatch r) ⊆ seedCoordBranch ∧
--       (∀ x ∈ closure (seedCoordPatch r), fderiv ℝ seedCoordImag x ≠ 0) ∧
--       ∀ (A : IntrinsicTensor), IntrinsicTensorSmooth A →
--         (∀ x v w, A x v w = A x w v) → (∀ x v, v ≠ 0 → 0 < A x v v) →
--         ∀ ρ : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ ρ → (∀ x, 0 < ρ x) →
--         (∀ y ∈ closedBall (0 : BaseModel) r,
--           dist ((intrinsicChartCoefficient A ρ seedPoint y,
--             fderiv ℝ (intrinsicChartCoefficient A ρ seedPoint) y) : CoefficientFirstJet BaseModel)
--             (roundCoefficientJet y) < δ) →
--         ∀ K : Set _root_.OAI.Yau.Jets.Coord, IsCompact K → K ⊆ seedCoordPatch r →
--         ∀ T : ℝ, Nonempty (PlacedEnvelopeData (intrinsicSeedCoordMetric A ρ) r a K T)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Geometry.CoefficientDerivative`, `OAI.Yau.Geometry.CoefficientPoint`, `OAI.Yau.Geometry.clmModule`, `OAI.Yau.Geometry.clmTopology` and `OAI.Yau.Jets.Coord` (definitions bundle `OAIQ237Ny000` of this split); `OAI.Yau.Target.BaseModel`, `OAI.Yau.Target.IntrinsicTensor`, `OAI.Yau.Target.IntrinsicTensorSmooth`, `OAI.Yau.Target.SphereCotangent` and `OAI.Yau.Target.seedPoint` (definitions bundle `OAIQ237Ny001` of this split); `OAI.Yau.Target.PlacedEnvelopeData`, `OAI.Yau.Target.intrinsicChartCoefficient`, `OAI.Yau.Target.roundCoefficientJet`, `OAI.Yau.Target.seedCoordBranch`, `OAI.Yau.Target.seedCoordCube` and `OAI.Yau.Target.seedCoordPatch` (definitions bundle `OAIQ237Ny002` of this split); `OAI.Yau.Target.intrinsicSeedCoordMetric` and `OAI.Yau.Target.seedCoordImag` (definitions bundle `OAIQ237Ny004` of this split); `OAI.Yau.Target.Base` (the published bundle `Def_YauCounterexample`).
--
--   **Used by.** The proof of `OAI.Yau.Target.intrinsic_packed_selected_stage` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Elliptic/IntrinsicNoncriticalPlacement.lean (declaration OAI.Yau.Target.intrinsic_noncritical_placed_data)

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.LinearAlgebra.Basis.Prod
import Mathlib.LinearAlgebra.Basis.SMul
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
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
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Yau.Jets Set Metric
open scoped ContDiff
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

theorem intrinsic_noncritical_placed_data : ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
    seedCoordCube a ⊆ seedCoordPatch r ∧ closure (seedCoordPatch r) ⊆ seedCoordBranch ∧
    (∀ x ∈ closure (seedCoordPatch r), fderiv ℝ seedCoordImag x ≠ 0) ∧
    ∀ (A : IntrinsicTensor), IntrinsicTensorSmooth A →
      (∀ x v w, A x v w = A x w v) → (∀ x v, v ≠ 0 → 0 < A x v v) →
      ∀ ρ : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ ρ → (∀ x, 0 < ρ x) →
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((intrinsicChartCoefficient A ρ seedPoint y,
          fderiv ℝ (intrinsicChartCoefficient A ρ seedPoint) y) : CoefficientFirstJet BaseModel)
          (roundCoefficientJet y) < δ) →
      ∀ K : Set _root_.OAI.Yau.Jets.Coord, IsCompact K → K ⊆ seedCoordPatch r →
      ∀ T : ℝ, Nonempty (PlacedEnvelopeData (intrinsicSeedCoordMetric A ρ) r a K T) := by
  sorry

end
end Yau.Target

end OAI
end
