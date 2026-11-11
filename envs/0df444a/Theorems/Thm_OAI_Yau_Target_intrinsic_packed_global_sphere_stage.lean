-- Prove2me | Theorems.Thm_OAI_Yau_Target_intrinsic_packed_global_sphere_stage
-- name    : OAI.Yau.Target.intrinsic_packed_global_sphere_stage
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:31:15.281662+00:00
-- url     : https://prove2.me/theorems/9d9cbcc8-37c7-47e0-a4c8-663f64ec58d7
-- title:
--   OAI.Yau.Target.intrinsic_packed_global_sphere_stage: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Target.intrinsic_packed_global_sphere_stage` of [lean/OAI/Geometry/NodalSets/Charts/IntrinsicPackedGlobalSphereStage.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Charts/IntrinsicPackedGlobalSphereStage.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Target`, with `open MeasureTheory Manifold Yau.Geometry Yau.Jets Yau.Probability Set Metric Filter`, `open scoped ContDiff Topology RealInnerProductSpace`):
--
--   ```lean
--   theorem intrinsic_packed_global_sphere_stage :
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
--         (∀ x ∉ K, rho x = 1) → ∃ c > 0, ∃ cn > 0, ∀ (T : ℝ) (J0 : ℕ),
--         let k0 := max 5 (J0+2)
--         let K' := 137*J0+269
--         ∃ d : PlacedEnvelopeData (intrinsicSeedCoordMetric A rho) r a (seedDeviationCoordinates K) T,
--         ∃ b : LocalCompactWaveData (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) d.S (closure d.U)
--           (3*(K'+3)+4*k0+6) ((K'+3)+k0+1) (K'+3) k0,
--         b.E ⊆ d.V ∧ ∃ C > 0, ∃ Q Qw : Set Yau.Jets.Coord,
--           IsCompact Qw ∧ Qw ⊆ d.Ω ∧
--           IsCompact Q ∧ Q ⊆ d.Ω ∧ closure d.U ⊆ interior Q ∧ seedDeviationCoordinates K ⊆ interior Q ∧
--           ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid d.U n),
--             letI := hfin
--             ∃ coeff : ((SourceGrid d.U n × Fin 3) × Fin 2) → ℝ,
--               let u := fun x ↦ seedCoordinateField n x + gaussianWaveField
--                 (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff x
--               let R0 := intrinsicRealCorrectionResidual A rho (seedEigenvalue n) u
--               let f := fun x ↦ R0 x / roundCorrectionDenominator u n x
--               let alpha := fun x ↦ f x*u x
--               let beta := Yau.densityCorrection roundCoordDensity u f (roundCoordGradient u) (seedEigenvalue n)
--               coeff ∈ coefficientEvent (n:ℝ) ∧ ContDiff ℝ ∞ u ∧
--               (∀ x ∈ closure d.Ω, ((n:ℝ)^65)⁻¹*max (Real.exp ((n:ℝ)*d.S x))
--                 (Real.exp ((n:ℝ)*seedCoordReal x)) ≤ sourceFirstJetSize u n x) ∧
--               ENNReal.ofReal (c*((n:ℝ)*(∫ x in seedCoordCube a,
--                 sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ≤
--                 Measure.hausdorffMeasure (4:ℝ)
--                   ((d.U ×ˢ Icc (-1:ℝ) 1) ∩ {y : Yau.Jets.Coord × ℝ | u y.1 = 0}) ∧
--               LiteralNodalCertificate (intrinsicSeedCoordMetric A rho) d.S (seedCoordCube a) d.U n u
--                 (c*((n:ℝ)*(∫ x in seedCoordCube a, sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ∧
--               ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ alpha ∧ ContDiff ℝ ∞ beta ∧
--               tsupport alpha ⊆ Q ∧ tsupport beta ⊆ Q ∧
--               (∀ x i, i ≤ J0 → ‖iteratedFDeriv ℝ i alpha x‖ + ‖iteratedFDeriv ℝ i beta x‖ ≤
--                 C*((n:ℝ)^2)⁻¹) ∧
--               (∀ x, Yau.weightedDiv roundCoordDensity
--                 (fun y i ↦ alpha y * roundCoordGradient u y i) x + seedEigenvalue n*beta x*u x = R0 x) ∧
--               ∃ ug ag bg : Base → ℝ,
--                 ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ ug ∧
--                 tsupport (ug-sphericalSeed n) ⊆ seedSphereFromCoord '' Qw ∧
--                 (∀ x, ug (seedSphereFromCoord x) = u x) ∧
--                 ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ ag ∧ ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ bg ∧
--                 tsupport ag ⊆ seedSphereFromCoord '' Q ∧ tsupport bg ⊆ seedSphereFromCoord '' Q ∧
--                 (∀ x, ag (seedSphereFromCoord x) = alpha x) ∧
--                 (∀ x, bg (seedSphereFromCoord x) = beta x) ∧
--                 (∀ x, |ag x| ≤ C*((n:ℝ)^2)⁻¹) ∧ (∀ x, |bg x| ≤ C*((n:ℝ)^2)⁻¹) ∧
--                 ∃ hnew : IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation ag x),
--                 ∃ hnewSym : (∀ x v w, (A x+roundTensorPerturbation ag x) v w =
--                   (A x+roundTensorPerturbation ag x) w v),
--                 ∃ hnewPos : (∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation ag x) v v),
--                 ∃ hrnew : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ rho x+bg x),
--                 ∃ hrnewPos : (∀ x, 0 < rho x+bg x), ug ≠ 0 ∧
--                 (∀ x, -intrinsicWeightedChartOperator (fun p ↦ A p+roundTensorPerturbation ag p)
--                   (fun p ↦ rho p+bg p) ug seedPoint (seedCoordEquiv x) = seedEigenvalue n*ug (seedSphereFromCoord x)) ∧
--                 (∀ x i j k, i ≤ J0 →
--                   ‖iteratedFDeriv ℝ i (fun y ↦ intrinsicSphereChartTensor (roundTensorPerturbation ag)
--                     seedPoint (seedCoordEquiv y) j k) x‖ ≤ C*((n:ℝ)^2)⁻¹) ∧
--                 (∀ p z, -intrinsicWeightedChartOperator (fun x ↦ A x+roundTensorPerturbation ag x)
--                   (fun x ↦ rho x+bg x) ug p z = seedEigenvalue n*ug ((extChartAt (𝓡 4) p).symm z)) ∧
--                 ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (circleLift ug) ∧ circleLift ug ≠ 0 ∧
--                 (∀ x : Manifold5, -chartLaplacian
--                   (intrinsicWeightedMetric (fun x ↦ A x+roundTensorPerturbation ag x) hnew hnewSym hnewPos
--                     (fun x ↦ rho x+bg x) hrnew hrnewPos)
--                   (extChartAt modelWithCorners x) (circleLift ug) (extChartAt modelWithCorners x x) =
--                     seedEigenvalue n*circleLift ug x) ∧
--                 0 < seedEigenvalue n ∧
--                 ENNReal.ofReal (cn*((n:ℝ)*(∫ x in seedCoordCube a,
--                   sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ≤
--                   nodalMeasure
--                     (intrinsicWeightedMetric (fun x ↦ A x+roundTensorPerturbation ag x) hnew hnewSym hnewPos
--                       (fun x ↦ rho x+bg x) hrnew hrnewPos) (circleLift ug) ∧
--                 ∃ eps > 0, ∀ vg : Base → ℝ,
--                   Continuous (fun x ↦ vg (seedSphereFromCoord x)) →
--                   (∀ x, |vg x-ug x| < eps) →
--                   ENNReal.ofReal (cn*((n:ℝ)*(∫ x in seedCoordCube a,
--                     sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ≤
--                     nodalMeasure
--                       (intrinsicWeightedMetric (fun x ↦ A x+roundTensorPerturbation ag x) hnew hnewSym hnewPos
--                         (fun x ↦ rho x+bg x) hrnew hrnewPos) (circleLift vg)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Coord`, `OAI.Yau.Geometry.CoefficientDerivative`, `OAI.Yau.Geometry.CoefficientPoint`, `OAI.Yau.Geometry.LiteralNodalCertificate`, `OAI.Yau.Geometry.LocalCompactWaveData`, `OAI.Yau.Geometry.SourceGrid`, `OAI.Yau.Geometry.clmAdd`, `OAI.Yau.Geometry.clmModule`, `OAI.Yau.Geometry.clmTopology`, `OAI.Yau.Geometry.gaussianWaveField`, `OAI.Yau.Geometry.latticeWave`, `OAI.Yau.Geometry.sourceFirstJetSize`, `OAI.Yau.Geometry.sourceSignScale`, `OAI.Yau.Jets.Coord` and `OAI.Yau.Probability.coefficientEvent` (definitions bundle `OAIQ237Ny000` of this split); `OAI.Yau.Target.AmbientBase`, `OAI.Yau.Target.BaseModel`, `OAI.Yau.Target.IntrinsicTensor`, `OAI.Yau.Target.IntrinsicTensorSmooth`, `OAI.Yau.Target.SphereCotangent`, `OAI.Yau.Target.circleLift`, `OAI.Yau.Target.seedEigenvalue`, `OAI.Yau.Target.seedPoint`, `OAI.Yau.Target.seedSpherePatch`, `OAI.Yau.Target.sphereCovectorRestriction` and `OAI.Yau.Target.sphericalSeed` (definitions bundle `OAIQ237Ny001` of this split); `OAI.Yau.weightedDiv`, `OAI.Yau.Target.PlacedEnvelopeData`, `OAI.Yau.Target.intrinsicChartCoefficient`, `OAI.Yau.Target.intrinsicGlobalSphereStageLocalInst1`, `OAI.Yau.Target.intrinsicGlobalSphereStageLocalInst11`, `OAI.Yau.Target.intrinsicGlobalSphereStageLocalInst2`, `OAI.Yau.Target.intrinsicGlobalSphereStageLocalInst9`, `OAI.Yau.Target.intrinsicSphereChartTensor`, `OAI.Yau.Target.roundCoefficientJet`, `OAI.Yau.Target.roundCoordDensity`, `OAI.Yau.Target.seedCoordBranch`, `OAI.Yau.Target.seedCoordCube`, `OAI.Yau.Target.seedCoordEquiv`, `OAI.Yau.Target.seedCoordPatch`, `OAI.Yau.Target.seedCoordReal` and `OAI.Yau.Target.seedSphereFromCoord` (definitions bundle `OAIQ237Ny002` of this split); `OAI.Yau.densityCorrection`, `OAI.Yau.Target.intrinsicRealCorrectionResidual`, `OAI.Yau.Target.intrinsicSeedCoordMetric`, `OAI.Yau.Target.intrinsicWeightedChartOperator`, `OAI.Yau.Target.intrinsicWeightedMetric`, `OAI.Yau.Target.roundCoordGradient`, `OAI.Yau.Target.roundCorrectionDenominator`, `OAI.Yau.Target.roundTensorPerturbation`, `OAI.Yau.Target.seedCoordWeight`, `OAI.Yau.Target.seedCoordinateField` and `OAI.Yau.Target.seedDeviationCoordinates` (definitions bundle `OAIQ237Ny004` of this split); `OAI.Yau.Target.Base`, `OAI.Yau.Target.Manifold5`, `OAI.Yau.Target.Model`, `OAI.Yau.Target.chartLaplacian`, `OAI.Yau.Target.modelWithCorners` and `OAI.Yau.Target.nodalMeasure` (the published bundle `Def_YauCounterexample`).
--
--   **Used by.** The proof of `OAI.Yau.Target.intrinsic_one_step` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Charts/IntrinsicPackedGlobalSphereStage.lean (declaration OAI.Yau.Target.intrinsic_packed_global_sphere_stage)

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
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.OperatorNorm
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
import Mathlib.Analysis.SpecificLimits.Basic
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
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
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
import Mathlib.Topology.Algebra.Support
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
attribute [local instance] intrinsicGlobalSphereStageLocalInst1 intrinsicGlobalSphereStageLocalInst2 intrinsicGlobalSphereStageLocalInst3 intrinsicGlobalSphereStageLocalInst4 intrinsicGlobalSphereStageLocalInst5 intrinsicGlobalSphereStageLocalInst6 intrinsicGlobalSphereStageLocalInst7 intrinsicGlobalSphereStageLocalInst8 intrinsicGlobalSphereStageLocalInst9 intrinsicGlobalSphereStageLocalInst10 intrinsicGlobalSphereStageLocalInst11 intrinsicGlobalSphereStageLocalInst12 intrinsicGlobalSphereStageLocalInst13 intrinsicGlobalSphereStageLocalInst14 intrinsicGlobalSphereStageLocalInst15 intrinsicGlobalSphereStageLocalInst16

theorem intrinsic_packed_global_sphere_stage :
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
      (∀ x ∉ K, rho x = 1) → ∃ c > 0, ∃ cn > 0, ∀ (T : ℝ) (J0 : ℕ),
      let k0 := max 5 (J0+2)
      let K' := 137*J0+269
      ∃ d : PlacedEnvelopeData (intrinsicSeedCoordMetric A rho) r a (seedDeviationCoordinates K) T,
      ∃ b : LocalCompactWaveData (intrinsicSeedCoordMetric A rho) (seedCoordWeight rho) d.S (closure d.U)
        (3*(K'+3)+4*k0+6) ((K'+3)+k0+1) (K'+3) k0,
      b.E ⊆ d.V ∧ ∃ C > 0, ∃ Q Qw : Set Yau.Jets.Coord,
        IsCompact Qw ∧ Qw ⊆ d.Ω ∧
        IsCompact Q ∧ Q ⊆ d.Ω ∧ closure d.U ⊆ interior Q ∧ seedDeviationCoordinates K ⊆ interior Q ∧
        ∀ᶠ n : ℕ in atTop, ∃ hfin : Fintype (SourceGrid d.U n),
          letI := hfin
          ∃ coeff : ((SourceGrid d.U n × Fin 3) × Fin 2) → ℝ,
            let u := fun x ↦ seedCoordinateField n x + gaussianWaveField
              (fun i : SourceGrid d.U n × Fin 3 ↦ latticeWave b.cover b.beams subset_closure n i.1 i.2) coeff x
            let R0 := intrinsicRealCorrectionResidual A rho (seedEigenvalue n) u
            let f := fun x ↦ R0 x / roundCorrectionDenominator u n x
            let alpha := fun x ↦ f x*u x
            let beta := Yau.densityCorrection roundCoordDensity u f (roundCoordGradient u) (seedEigenvalue n)
            coeff ∈ coefficientEvent (n:ℝ) ∧ ContDiff ℝ ∞ u ∧
            (∀ x ∈ closure d.Ω, ((n:ℝ)^65)⁻¹*max (Real.exp ((n:ℝ)*d.S x))
              (Real.exp ((n:ℝ)*seedCoordReal x)) ≤ sourceFirstJetSize u n x) ∧
            ENNReal.ofReal (c*((n:ℝ)*(∫ x in seedCoordCube a,
              sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ≤
              Measure.hausdorffMeasure (4:ℝ)
                ((d.U ×ˢ Icc (-1:ℝ) 1) ∩ {y : Yau.Jets.Coord × ℝ | u y.1 = 0}) ∧
            LiteralNodalCertificate (intrinsicSeedCoordMetric A rho) d.S (seedCoordCube a) d.U n u
              (c*((n:ℝ)*(∫ x in seedCoordCube a, sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ∧
            ContDiff ℝ ∞ f ∧ ContDiff ℝ ∞ alpha ∧ ContDiff ℝ ∞ beta ∧
            tsupport alpha ⊆ Q ∧ tsupport beta ⊆ Q ∧
            (∀ x i, i ≤ J0 → ‖iteratedFDeriv ℝ i alpha x‖ + ‖iteratedFDeriv ℝ i beta x‖ ≤
              C*((n:ℝ)^2)⁻¹) ∧
            (∀ x, Yau.weightedDiv roundCoordDensity
              (fun y i ↦ alpha y * roundCoordGradient u y i) x + seedEigenvalue n*beta x*u x = R0 x) ∧
            ∃ ug ag bg : Base → ℝ,
              ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ ug ∧
              tsupport (ug-sphericalSeed n) ⊆ seedSphereFromCoord '' Qw ∧
              (∀ x, ug (seedSphereFromCoord x) = u x) ∧
              ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ ag ∧ ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ bg ∧
              tsupport ag ⊆ seedSphereFromCoord '' Q ∧ tsupport bg ⊆ seedSphereFromCoord '' Q ∧
              (∀ x, ag (seedSphereFromCoord x) = alpha x) ∧
              (∀ x, bg (seedSphereFromCoord x) = beta x) ∧
              (∀ x, |ag x| ≤ C*((n:ℝ)^2)⁻¹) ∧ (∀ x, |bg x| ≤ C*((n:ℝ)^2)⁻¹) ∧
              ∃ hnew : IntrinsicTensorSmooth (fun x ↦ A x+roundTensorPerturbation ag x),
              ∃ hnewSym : (∀ x v w, (A x+roundTensorPerturbation ag x) v w =
                (A x+roundTensorPerturbation ag x) w v),
              ∃ hnewPos : (∀ x v, v ≠ 0 → 0 < (A x+roundTensorPerturbation ag x) v v),
              ∃ hrnew : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (fun x ↦ rho x+bg x),
              ∃ hrnewPos : (∀ x, 0 < rho x+bg x), ug ≠ 0 ∧
              (∀ x, -intrinsicWeightedChartOperator (fun p ↦ A p+roundTensorPerturbation ag p)
                (fun p ↦ rho p+bg p) ug seedPoint (seedCoordEquiv x) = seedEigenvalue n*ug (seedSphereFromCoord x)) ∧
              (∀ x i j k, i ≤ J0 →
                ‖iteratedFDeriv ℝ i (fun y ↦ intrinsicSphereChartTensor (roundTensorPerturbation ag)
                  seedPoint (seedCoordEquiv y) j k) x‖ ≤ C*((n:ℝ)^2)⁻¹) ∧
              (∀ p z, -intrinsicWeightedChartOperator (fun x ↦ A x+roundTensorPerturbation ag x)
                (fun x ↦ rho x+bg x) ug p z = seedEigenvalue n*ug ((extChartAt (𝓡 4) p).symm z)) ∧
              ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (circleLift ug) ∧ circleLift ug ≠ 0 ∧
              (∀ x : Manifold5, -chartLaplacian
                (intrinsicWeightedMetric (fun x ↦ A x+roundTensorPerturbation ag x) hnew hnewSym hnewPos
                  (fun x ↦ rho x+bg x) hrnew hrnewPos)
                (extChartAt modelWithCorners x) (circleLift ug) (extChartAt modelWithCorners x x) =
                  seedEigenvalue n*circleLift ug x) ∧
              0 < seedEigenvalue n ∧
              ENNReal.ofReal (cn*((n:ℝ)*(∫ x in seedCoordCube a,
                sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ≤
                nodalMeasure
                  (intrinsicWeightedMetric (fun x ↦ A x+roundTensorPerturbation ag x) hnew hnewSym hnewPos
                    (fun x ↦ rho x+bg x) hrnew hrnewPos) (circleLift ug) ∧
              ∃ eps > 0, ∀ vg : Base → ℝ,
                Continuous (fun x ↦ vg (seedSphereFromCoord x)) →
                (∀ x, |vg x-ug x| < eps) →
                ENNReal.ofReal (cn*((n:ℝ)*(∫ x in seedCoordCube a,
                  sourceSignScale (intrinsicSeedCoordMetric A rho) d.S x))) ≤
                  nodalMeasure
                    (intrinsicWeightedMetric (fun x ↦ A x+roundTensorPerturbation ag x) hnew hnewSym hnewPos
                      (fun x ↦ rho x+bg x) hrnew hrnewPos) (circleLift vg) := by
  sorry

end
end Yau.Target

end OAI
end
