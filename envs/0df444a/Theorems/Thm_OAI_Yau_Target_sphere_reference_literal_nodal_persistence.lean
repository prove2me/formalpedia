-- Prove2me | Theorems.Thm_OAI_Yau_Target_sphere_reference_literal_nodal_persistence
-- name    : OAI.Yau.Target.sphere_reference_literal_nodal_persistence
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:35:53.711087+00:00
-- url     : https://prove2.me/theorems/2475e622-a198-44b6-95b3-9e3b5a0d0841
-- title:
--   OAI.Yau.Target.sphere_reference_literal_nodal_persistence: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Target.sphere_reference_literal_nodal_persistence` of [lean/OAI/Geometry/NodalSets/Persistence/SphereReferenceNodalPersistence.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Persistence/SphereReferenceNodalPersistence.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Target`, with `open Manifold MeasureTheory Set Yau.Geometry`, `open scoped ContDiff ENNReal NNReal`):
--
--   ```lean
--   theorem sphere_reference_literal_nodal_persistence
--       (P₀ : Finset Base)
--       (hcover : ∀ x : Base, ∃ p ∈ P₀, ∃ y ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm y=x)
--       (d₀ : SphereEnergyData) (hd₀ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d₀.density)
--       {H : Set Yau.Jets.Coord} (hH : IsCompact H) :
--       ∃ delta > 0, ∃ C : ℝ≥0, 0 < C ∧
--         ∀ (d : SphereEnergyData), ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density →
--           sphereCoefficientDistance P₀ 0 d₀.tensor d₀.density d.tensor d.density < delta →
--           ∀ (u : Base → ℝ), ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u → u ≠ 0 →
--           ∀ lam > 0,
--             (∀ p y, -intrinsicWeightedChartOperator d.tensor d.density u p y =
--               lam*u ((extChartAt (𝓡 4) p).symm y)) →
--             (∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
--               (∀ p y, -intrinsicWeightedChartOperator d.tensor d.density v p y =
--                 lam*v ((extChartAt (𝓡 4) p).symm y)) → ∃ c : ℝ, v=c • u) →
--             ∀ (g : Yau.Jets.Coord → Yau.Jets.Coord →L[ℝ] Yau.Jets.Coord →L[ℝ] ℝ)
--               (S : Yau.Jets.Coord → ℝ) (Q U : Set Yau.Jets.Coord) (n : ℕ) (M : ℝ),
--               U ⊆ H → LiteralNodalCertificate g S Q U n (fun x ↦ u (seedSphereFromCoord x)) M →
--               ∃ N : ℕ, sphereIndexedEigenvalue d N=lam ∧
--                 ∃ P : Finset Base, P₀ ⊆ P ∧
--                   ∃ eta > 0, ∀ (b : SphereEnergyData) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density),
--                     sphereCoefficientDistance P 8 d.tensor d.density b.tensor b.density < eta →
--                     sphereIndexedEigenvalue b N ∈ Icc (lam/2) (2*lam) ∧
--                     ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
--                       (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density v p y =
--                         sphereIndexedEigenvalue b N*v ((extChartAt (𝓡 4) p).symm y)) ∧
--                       ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (circleLift v) ∧ circleLift v ≠ 0 ∧
--                       (∀ x : Manifold5, -chartLaplacian
--                         (intrinsicWeightedMetric b.tensor b.smooth b.symm b.pos b.density hb b.positive)
--                         (extChartAt modelWithCorners x) (circleLift v) (extChartAt modelWithCorners x x) =
--                           sphereIndexedEigenvalue b N*circleLift v x) ∧
--                       ENNReal.ofReal (M/(C:ℝ)^4) ≤ nodalMeasure
--                         (intrinsicWeightedMetric b.tensor b.smooth b.symm b.pos b.density hb b.positive) (circleLift v)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Geometry.LiteralNodalCertificate` and `OAI.Yau.Jets.Coord` (definitions bundle `OAIQ237Ny000` of this split); `OAI.Yau.Target.BaseModel` and `OAI.Yau.Target.circleLift` (definitions bundle `OAIQ237Ny001` of this split); `OAI.Yau.Target.SphereEnergyData`, `OAI.Yau.Target.seedSphereFromCoord` and `OAI.Yau.Target.sphereAtlasCore` (definitions bundle `OAIQ237Ny002` of this split); `OAI.Yau.Target.intrinsicWeightedChartOperator`, `OAI.Yau.Target.intrinsicWeightedMetric`, `OAI.Yau.Target.sphereCoefficientDistance` and `OAI.Yau.Target.sphereIndexedEigenvalue` (definitions bundle `OAIQ237Ny004` of this split); `OAI.Yau.Target.Base`, `OAI.Yau.Target.Manifold5`, `OAI.Yau.Target.Model`, `OAI.Yau.Target.chartLaplacian`, `OAI.Yau.Target.modelWithCorners` and `OAI.Yau.Target.nodalMeasure` (the published bundle `Def_YauCounterexample`).
--
--   **Used by.** The proof of `OAI.Yau.Target.intrinsic_one_step` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Persistence/SphereReferenceNodalPersistence.lean (declaration OAI.Yau.Target.sphere_reference_literal_nodal_persistence)

import Mathlib
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finsupp.Weight
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Int.Interval
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.OfFn
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Geometry.Manifold.Algebra.LieGroup
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.Riemannian.Basic
import Mathlib.Geometry.Manifold.SmoothApprox
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
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
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
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.UniformSpace.UniformConvergence
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold MeasureTheory Set Yau.Geometry
open scoped ContDiff ENNReal NNReal
noncomputable section

theorem sphere_reference_literal_nodal_persistence
    (P₀ : Finset Base)
    (hcover : ∀ x : Base, ∃ p ∈ P₀, ∃ y ∈ sphereAtlasCore, (extChartAt (𝓡 4) p).symm y=x)
    (d₀ : SphereEnergyData) (hd₀ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d₀.density)
    {H : Set Yau.Jets.Coord} (hH : IsCompact H) :
    ∃ delta > 0, ∃ C : ℝ≥0, 0 < C ∧
      ∀ (d : SphereEnergyData), ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density →
        sphereCoefficientDistance P₀ 0 d₀.tensor d₀.density d.tensor d.density < delta →
        ∀ (u : Base → ℝ), ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u → u ≠ 0 →
        ∀ lam > 0,
          (∀ p y, -intrinsicWeightedChartOperator d.tensor d.density u p y =
            lam*u ((extChartAt (𝓡 4) p).symm y)) →
          (∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
            (∀ p y, -intrinsicWeightedChartOperator d.tensor d.density v p y =
              lam*v ((extChartAt (𝓡 4) p).symm y)) → ∃ c : ℝ, v=c • u) →
          ∀ (g : Yau.Jets.Coord → Yau.Jets.Coord →L[ℝ] Yau.Jets.Coord →L[ℝ] ℝ)
            (S : Yau.Jets.Coord → ℝ) (Q U : Set Yau.Jets.Coord) (n : ℕ) (M : ℝ),
            U ⊆ H → LiteralNodalCertificate g S Q U n (fun x ↦ u (seedSphereFromCoord x)) M →
            ∃ N : ℕ, sphereIndexedEigenvalue d N=lam ∧
              ∃ P : Finset Base, P₀ ⊆ P ∧
                ∃ eta > 0, ∀ (b : SphereEnergyData) (hb : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density),
                  sphereCoefficientDistance P 8 d.tensor d.density b.tensor b.density < eta →
                  sphereIndexedEigenvalue b N ∈ Icc (lam/2) (2*lam) ∧
                  ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
                    (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density v p y =
                      sphereIndexedEigenvalue b N*v ((extChartAt (𝓡 4) p).symm y)) ∧
                    ContMDiff modelWithCorners 𝓘(ℝ,ℝ) ∞ (circleLift v) ∧ circleLift v ≠ 0 ∧
                    (∀ x : Manifold5, -chartLaplacian
                      (intrinsicWeightedMetric b.tensor b.smooth b.symm b.pos b.density hb b.positive)
                      (extChartAt modelWithCorners x) (circleLift v) (extChartAt modelWithCorners x x) =
                        sphereIndexedEigenvalue b N*circleLift v x) ∧
                    ENNReal.ofReal (M/(C:ℝ)^4) ≤ nodalMeasure
                      (intrinsicWeightedMetric b.tensor b.smooth b.symm b.pos b.density hb b.positive) (circleLift v) := by
  sorry

end
end Yau.Target

end OAI
end
