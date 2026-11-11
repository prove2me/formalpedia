-- Prove2me | Theorems.Thm_OAI_Yau_Target_sphere_eigen_global_neighborhood_compactness
-- name    : OAI.Yau.Target.sphere_eigen_global_neighborhood_compactness
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:32:31.338244+00:00
-- url     : https://prove2.me/theorems/05cc4acc-ea85-4270-abd5-4f1fbc9a28a1
-- title:
--   OAI.Yau.Target.sphere_eigen_global_neighborhood_compactness: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Target.sphere_eigen_global_neighborhood_compactness` of [lean/OAI/Geometry/NodalSets/Charts/SphereGlobalNeighborhoodCompactness.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Charts/SphereGlobalNeighborhoodCompactness.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Target`, with `open MeasureTheory Manifold Set Metric Filter Yau.Geometry Yau.Analysis`, `open scoped ContDiff Topology`):
--
--   ```lean
--   theorem sphere_eigen_global_neighborhood_compactness (d₀ : SphereEnergyData)
--       (hrho₀ : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d₀.density (sphereChartCoordMap p x)))
--       (mu₀ : ℝ) (n : ℕ) :
--       ∃ P : Finset Base,
--         (∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) (1/512),
--           sphereChartCoordMap p z=x) ∧
--         ∃ eps > 0, ∀ (d : ℕ → SphereEnergyData) (mu : ℕ → ℝ),
--           (∀ j p, ContDiff ℝ ∞ (fun x ↦ (d j).density (sphereChartCoordMap p x))) →
--           (∀ j, mu j ≠ 0) →
--           (∀ j p, p ∈ P → ∀ x ∈ closedBall (0 : Yau.Jets.Coord) (1/128),
--             ∀ es : List (Fin 4), es.length ≤ n+6 →
--               (∀ a b, |partialJet (fun z ↦ sphereChartPrincipalDensity (d j) p z a b) es x-
--                 partialJet (fun z ↦ sphereChartPrincipalDensity d₀ p z a b) es x| ≤ eps) ∧
--               |partialJet (sphereEigenForcingCoefficient (d j) p (mu j)) es x-
--                 partialJet (sphereEigenForcingCoefficient d₀ p mu₀) es x| ≤ eps) →
--           (∀ j p, p ∈ P → ∀ x ∈ closedBall (0 : Yau.Jets.Coord) (1/128),
--             |roundCoordDensity x*(d j).density (sphereChartCoordMap p x)-
--               roundCoordDensity x*d₀.density (sphereChartCoordMap p x)| ≤ eps) →
--           ∀ f : ∀ j, SphereWeightedL2 (d j),
--             (∀ j, sphereL2Resolvent (d j) (f j)=mu j • f j) → (∀ j, ‖f j‖=1) →
--           ∃ u : ℕ → Base → ℝ,
--             (∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (u j)) ∧
--             (∀ j, u j =ᵐ[sphereWeightedMeasure (d j).density] (f j : Base → ℝ)) ∧
--             (∀ j, sphereWeightedPairing (d j).density (u j) (u j)=1) ∧
--             (∀ j, u j ≠ 0) ∧
--             ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) n v ∧
--               ∃ nu : ℕ → ℕ, StrictMono nu ∧ TendstoUniformly (fun j ↦ u (nu j)) v atTop ∧
--                 (∀ p ∈ P, ∀ ds : List (Fin 4), ds.length ≤ n →
--                   TendstoUniformlyOn (fun j ↦ partialJet (u (nu j) ∘ sphereChartCoordMap p) ds)
--                     (partialJet (v ∘ sphereChartCoordMap p) ds) atTop (ball 0 (1/256))) ∧
--                 (TendstoUniformly (fun j ↦ (d j).density) d₀.density atTop →
--                   sphereWeightedPairing d₀.density v v=1 ∧ v ≠ 0)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Analysis.partialJet` and `OAI.Yau.Jets.Coord` (definitions bundle `OAIQ237Ny000` of this split); `OAI.Yau.Target.sphereWeightedL2Measurable` (definitions bundle `OAIQ237Ny001` of this split); `OAI.Yau.Target.SphereEnergyData`, `OAI.Yau.Target.roundCoordDensity`, `OAI.Yau.Target.sphereChartCoordMap` and `OAI.Yau.Target.sphereWeightedPairing` (definitions bundle `OAIQ237Ny002` of this split); `OAI.Yau.Target.SphereWeightedL2`, `OAI.Yau.Target.sphereChartPrincipalDensity`, `OAI.Yau.Target.sphereEigenForcingCoefficient`, `OAI.Yau.Target.sphereL2Resolvent` and `OAI.Yau.Target.sphereWeightedMeasure` (definitions bundle `OAIQ237Ny004` of this split); `OAI.Yau.Target.Base` (the published bundle `Def_YauCounterexample`).
--
--   **Used by.** The proof of `OAI.Yau.Target.sphere_finite_norm_indexed_compactness` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Charts/SphereGlobalNeighborhoodCompactness.lean (declaration OAI.Yau.Target.sphere_eigen_global_neighborhood_compactness)

import Mathlib
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
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
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
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
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
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
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
open MeasureTheory Manifold Set Metric Filter Yau.Geometry Yau.Analysis
open scoped ContDiff Topology
noncomputable section

local instance sphereGlobalCompactMeasurable_rdee615_1 : MeasurableSpace Base := borel Base
local instance sphereGlobalCompactBorel_rdee615_1 : BorelSpace Base := ⟨rfl⟩
theorem sphere_eigen_global_neighborhood_compactness (d₀ : SphereEnergyData)
    (hrho₀ : ∀ p : Base, ContDiff ℝ ∞ (fun x ↦ d₀.density (sphereChartCoordMap p x)))
    (mu₀ : ℝ) (n : ℕ) :
    ∃ P : Finset Base,
      (∀ x : Base, ∃ p ∈ P, ∃ z ∈ ball (0 : Yau.Jets.Coord) (1/512),
        sphereChartCoordMap p z=x) ∧
      ∃ eps > 0, ∀ (d : ℕ → SphereEnergyData) (mu : ℕ → ℝ),
        (∀ j p, ContDiff ℝ ∞ (fun x ↦ (d j).density (sphereChartCoordMap p x))) →
        (∀ j, mu j ≠ 0) →
        (∀ j p, p ∈ P → ∀ x ∈ closedBall (0 : Yau.Jets.Coord) (1/128),
          ∀ es : List (Fin 4), es.length ≤ n+6 →
            (∀ a b, |partialJet (fun z ↦ sphereChartPrincipalDensity (d j) p z a b) es x-
              partialJet (fun z ↦ sphereChartPrincipalDensity d₀ p z a b) es x| ≤ eps) ∧
            |partialJet (sphereEigenForcingCoefficient (d j) p (mu j)) es x-
              partialJet (sphereEigenForcingCoefficient d₀ p mu₀) es x| ≤ eps) →
        (∀ j p, p ∈ P → ∀ x ∈ closedBall (0 : Yau.Jets.Coord) (1/128),
          |roundCoordDensity x*(d j).density (sphereChartCoordMap p x)-
            roundCoordDensity x*d₀.density (sphereChartCoordMap p x)| ≤ eps) →
        ∀ f : ∀ j, SphereWeightedL2 (d j),
          (∀ j, sphereL2Resolvent (d j) (f j)=mu j • f j) → (∀ j, ‖f j‖=1) →
        ∃ u : ℕ → Base → ℝ,
          (∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (u j)) ∧
          (∀ j, u j =ᵐ[sphereWeightedMeasure (d j).density] (f j : Base → ℝ)) ∧
          (∀ j, sphereWeightedPairing (d j).density (u j) (u j)=1) ∧
          (∀ j, u j ≠ 0) ∧
          ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) n v ∧
            ∃ nu : ℕ → ℕ, StrictMono nu ∧ TendstoUniformly (fun j ↦ u (nu j)) v atTop ∧
              (∀ p ∈ P, ∀ ds : List (Fin 4), ds.length ≤ n →
                TendstoUniformlyOn (fun j ↦ partialJet (u (nu j) ∘ sphereChartCoordMap p) ds)
                  (partialJet (v ∘ sphereChartCoordMap p) ds) atTop (ball 0 (1/256))) ∧
              (TendstoUniformly (fun j ↦ (d j).density) d₀.density atTop →
                sphereWeightedPairing d₀.density v v=1 ∧ v ≠ 0) := by
  sorry

end
end Yau.Target

end OAI
end
