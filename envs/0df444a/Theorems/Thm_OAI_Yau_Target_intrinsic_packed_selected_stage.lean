-- Prove2me | Theorems.Thm_OAI_Yau_Target_intrinsic_packed_selected_stage
-- name    : OAI.Yau.Target.intrinsic_packed_selected_stage
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:32:04.047689+00:00
-- url     : https://prove2.me/theorems/b2a6c92a-1228-4df5-9399-4067ad7072bd
-- title:
--   OAI.Yau.Target.intrinsic_packed_selected_stage: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Target.intrinsic_packed_selected_stage` of [lean/OAI/Geometry/NodalSets/Elliptic/IntrinsicPackedSelectedStage.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Elliptic/IntrinsicPackedSelectedStage.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Target`, with `open MeasureTheory Manifold Yau.Geometry Yau.Jets Yau.Probability Set Metric Filter`, `open scoped ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem intrinsic_packed_selected_stage :
--       ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
--         seedCoordCube a ⊆ seedCoordPatch r ∧ closure (seedCoordPatch r) ⊆ seedCoordBranch ∧
--         ∀ (A : IntrinsicTensor), IntrinsicTensorSmooth A →
--           (∀ x v w, A x v w = A x w v) → (∀ x v, v ≠ 0 → 0 < A x v v) →
--         ∀ rho : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho → (∀ x, 0 < rho x) →
--         (∀ y ∈ closedBall (0 : BaseModel) r,
--           dist ((intrinsicChartCoefficient A rho seedPoint y,
--             fderiv ℝ (intrinsicChartCoefficient A rho seedPoint) y) : CoefficientFirstJet BaseModel)
--             (roundCoefficientJet y) < δ) →
--         ∀ K : Set Base, IsCompact K → K ⊆ seedSpherePatch r →
--         (∀ x ∉ K, ∀ v w : AmbientBase,
--           ⟪(x:AmbientBase),v⟫ = 0 → ⟪(x:AmbientBase),w⟫ = 0 →
--           A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = ⟪v,w⟫) →
--         (∀ x ∉ K, rho x = 1) → ∃ c > 0, ∀ (T : ℝ) (k0 K' : ℕ), 5 ≤ k0 →
--         ∃ d : PlacedEnvelopeData (intrinsicSeedCoordMetric A rho) r a (seedDeviationCoordinates K) T,
--       ∃ b : LocalCompactWaveData (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) d.S (closure d.U)
--           (3*(K'+3)+4*k0+6) ((K'+3)+k0+1) (K'+3) k0,
--         b.E ⊆ d.V ∧ ∃ C > 0, ∃ Q : Set _root_.OAI.Yau.Jets.Coord,
--           IsCompact Q ∧ Q ⊆ d.Ω ∧ closure d.U ⊆ interior Q ∧ seedDeviationCoordinates K ⊆ interior Q ∧
--           ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid d.U n),
--             letI := hfin
--             ∃ coeff : ((SourceGrid d.U n × Fin 3) × Fin 2) → ℝ,
--               let v := gaussianWaveField
--                 (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff
--               let u := fun x ↦ seedCoordinateField n x+v x
--               let R := realSourceResidual (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) (seedEigenvalue n)
--               coeff ∈ coefficientEvent (n:ℝ) ∧
--               ContDiff ℝ ∞ u ∧ ContDiff ℝ ∞ (R u) ∧
--               R u = (fun x ↦ R (seedCoordinateField n) x+R v x) ∧
--               tsupport (R u) ⊆ Q ∧
--               (∀ x ∉ Q, ∀ k : ℕ, iteratedFDeriv ℝ k (R u) x = 0) ∧
--               (∀ x : _root_.OAI.Yau.Jets.Coord,
--                 DerivativeBound k0 (R u) x
--                   (C*(n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*d.S x))) ∧
--               (∀ x ∈ closure d.Ω, ((n:ℝ)^65)⁻¹*max (Real.exp ((n:ℝ)*d.S x))
--                 (Real.exp ((n:ℝ)*seedCoordReal x)) ≤ sourceFirstJetSize u n x) ∧
--               ENNReal.ofReal (c*((n:ℝ)*(∫ x in seedCoordCube a,
--                 sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ≤
--                 Measure.hausdorffMeasure (4:ℝ)
--                   ((d.U ×ˢ Icc (-1:ℝ) 1) ∩ {y : _root_.OAI.Yau.Jets.Coord × ℝ | u y.1 = 0}) ∧
--               LiteralNodalCertificate (intrinsicSeedCoordMetric A rho) d.S (seedCoordCube a) d.U n u
--                 (c*((n:ℝ)*(∫ x in seedCoordCube a, sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Geometry.CoefficientDerivative`, `OAI.Yau.Geometry.CoefficientPoint`, `OAI.Yau.Geometry.LiteralNodalCertificate`, `OAI.Yau.Geometry.LocalCompactWaveData`, `OAI.Yau.Geometry.SourceGrid`, `OAI.Yau.Geometry.clmModule`, `OAI.Yau.Geometry.clmTopology`, `OAI.Yau.Geometry.gaussianWaveField`, `OAI.Yau.Geometry.latticeWave`, `OAI.Yau.Geometry.sourceFirstJetSize`, `OAI.Yau.Geometry.sourceSignScale`, `OAI.Yau.Jets.Coord`, `OAI.Yau.Jets.DerivativeBound` and `OAI.Yau.Probability.coefficientEvent` (definitions bundle `OAIQ237Ny000` of this split); `OAI.Yau.Target.AmbientBase`, `OAI.Yau.Target.BaseModel`, `OAI.Yau.Target.IntrinsicTensor`, `OAI.Yau.Target.IntrinsicTensorSmooth`, `OAI.Yau.Target.SphereCotangent`, `OAI.Yau.Target.seedEigenvalue`, `OAI.Yau.Target.seedPoint`, `OAI.Yau.Target.seedSpherePatch` and `OAI.Yau.Target.sphereCovectorRestriction` (definitions bundle `OAIQ237Ny001` of this split); `OAI.Yau.Geometry.realSourceResidual`, `OAI.Yau.Target.PlacedEnvelopeData`, `OAI.Yau.Target.intrinsicChartCoefficient`, `OAI.Yau.Target.roundCoefficientJet`, `OAI.Yau.Target.seedCoordBranch`, `OAI.Yau.Target.seedCoordCube`, `OAI.Yau.Target.seedCoordPatch` and `OAI.Yau.Target.seedCoordReal` (definitions bundle `OAIQ237Ny002` of this split); `OAI.Yau.Target.intrinsicSeedCoordMetric`, `OAI.Yau.Target.seedCoordWeight`, `OAI.Yau.Target.seedCoordinateField` and `OAI.Yau.Target.seedDeviationCoordinates` (definitions bundle `OAIQ237Ny004` of this split); `OAI.Yau.Target.Base` (the published bundle `Def_YauCounterexample`).
--
--   **Used by.** The proof of `OAI.Yau.Target.intrinsic_packed_small_corrected_stage` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Elliptic/IntrinsicPackedSelectedStage.lean (declaration OAI.Yau.Target.intrinsic_packed_selected_stage)

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pi
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
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.FinRange
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Choose.Sum
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
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Moments.Covariance
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
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
open MeasureTheory Manifold Yau.Geometry Yau.Jets Yau.Probability Set Metric Filter
open scoped ContDiff Topology RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule

theorem intrinsic_packed_selected_stage :
    ∃ r a δ : ℝ, 0 < r ∧ 0 < a ∧ 0 < δ ∧
      seedCoordCube a ⊆ seedCoordPatch r ∧ closure (seedCoordPatch r) ⊆ seedCoordBranch ∧
      ∀ (A : IntrinsicTensor), IntrinsicTensorSmooth A →
        (∀ x v w, A x v w = A x w v) → (∀ x v, v ≠ 0 → 0 < A x v v) →
      ∀ rho : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ rho → (∀ x, 0 < rho x) →
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((intrinsicChartCoefficient A rho seedPoint y,
          fderiv ℝ (intrinsicChartCoefficient A rho seedPoint) y) : CoefficientFirstJet BaseModel)
          (roundCoefficientJet y) < δ) →
      ∀ K : Set Base, IsCompact K → K ⊆ seedSpherePatch r →
      (∀ x ∉ K, ∀ v w : AmbientBase,
        ⟪(x:AmbientBase),v⟫ = 0 → ⟪(x:AmbientBase),w⟫ = 0 →
        A x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w) = ⟪v,w⟫) →
      (∀ x ∉ K, rho x = 1) → ∃ c > 0, ∀ (T : ℝ) (k0 K' : ℕ), 5 ≤ k0 →
      ∃ d : PlacedEnvelopeData (intrinsicSeedCoordMetric A rho) r a (seedDeviationCoordinates K) T,
    ∃ b : LocalCompactWaveData (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) d.S (closure d.U)
        (3*(K'+3)+4*k0+6) ((K'+3)+k0+1) (K'+3) k0,
      b.E ⊆ d.V ∧ ∃ C > 0, ∃ Q : Set _root_.OAI.Yau.Jets.Coord,
        IsCompact Q ∧ Q ⊆ d.Ω ∧ closure d.U ⊆ interior Q ∧ seedDeviationCoordinates K ⊆ interior Q ∧
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid d.U n),
          letI := hfin
          ∃ coeff : ((SourceGrid d.U n × Fin 3) × Fin 2) → ℝ,
            let v := gaussianWaveField
              (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff
            let u := fun x ↦ seedCoordinateField n x+v x
            let R := realSourceResidual (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) (seedEigenvalue n)
            coeff ∈ coefficientEvent (n:ℝ) ∧
            ContDiff ℝ ∞ u ∧ ContDiff ℝ ∞ (R u) ∧
            R u = (fun x ↦ R (seedCoordinateField n) x+R v x) ∧
            tsupport (R u) ⊆ Q ∧
            (∀ x ∉ Q, ∀ k : ℕ, iteratedFDeriv ℝ k (R u) x = 0) ∧
            (∀ x : _root_.OAI.Yau.Jets.Coord,
              DerivativeBound k0 (R u) x
                (C*(n:ℝ)^(-(K':ℝ))*Real.exp ((n:ℝ)*d.S x))) ∧
            (∀ x ∈ closure d.Ω, ((n:ℝ)^65)⁻¹*max (Real.exp ((n:ℝ)*d.S x))
              (Real.exp ((n:ℝ)*seedCoordReal x)) ≤ sourceFirstJetSize u n x) ∧
            ENNReal.ofReal (c*((n:ℝ)*(∫ x in seedCoordCube a,
              sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ≤
              Measure.hausdorffMeasure (4:ℝ)
                ((d.U ×ˢ Icc (-1:ℝ) 1) ∩ {y : _root_.OAI.Yau.Jets.Coord × ℝ | u y.1 = 0}) ∧
            LiteralNodalCertificate (intrinsicSeedCoordMetric A rho) d.S (seedCoordCube a) d.U n u
              (c*((n:ℝ)*(∫ x in seedCoordCube a, sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) := by
  sorry

end
end Yau.Target

end OAI
end
