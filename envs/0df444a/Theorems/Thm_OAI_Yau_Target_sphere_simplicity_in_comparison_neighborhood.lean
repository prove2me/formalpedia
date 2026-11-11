-- Prove2me | Theorems.Thm_OAI_Yau_Target_sphere_simplicity_in_comparison_neighborhood
-- name    : OAI.Yau.Target.sphere_simplicity_in_comparison_neighborhood
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:34:55.616965+00:00
-- url     : https://prove2.me/theorems/8bf6348c-8a8b-435b-b69e-a74b17f0b529
-- title:
--   OAI.Yau.Target.sphere_simplicity_in_comparison_neighborhood: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Target.sphere_simplicity_in_comparison_neighborhood` of [lean/OAI/Geometry/NodalSets/Charts/SphereSimplicityInNeighborhood.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Charts/SphereSimplicityInNeighborhood.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Target`, with `open Manifold Yau.Geometry Set Metric`, `open scoped ContDiff RealInnerProductSpace`):
--
--   ```lean
--   theorem sphere_simplicity_in_comparison_neighborhood
--       (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
--       {r delta : ℝ} (hr : 0 < r)
--       (hclose : ∀ y ∈ closedBall (0 : BaseModel) r,
--         dist ((intrinsicChartCoefficient d.tensor d.density seedPoint y,
--           fderiv ℝ (intrinsicChartCoefficient d.tensor d.density seedPoint) y) : CoefficientFirstJet BaseModel)
--           (roundCoefficientJet y) < delta)
--       (K : Set Base) (hK : IsCompact K) (hKP : K ⊆ seedSpherePatch r)
--       (hA : ∀ x ∉ K, ∀ v w : AmbientBase, ⟪(x:AmbientBase),v⟫=0 → ⟪(x:AmbientBase),w⟫=0 →
--         d.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)=⟪v,w⟫)
--       (hrho : ∀ x ∉ K, d.density x=1)
--       (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u ≠ 0)
--       (lam : ℝ) (hlam : 0 < lam)
--       (he : ∀ p y, -intrinsicWeightedChartOperator d.tensor d.density u p y =
--         lam*u ((extChartAt (𝓡 4) p).symm y))
--       (P : Finset Base) (J : ℕ) (eps : ℝ) (heps : 0 < eps) :
--       ∃ (b : SphereEnergyData) (_ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density),
--         sphereCoefficientDistance P J d.tensor d.density b.tensor b.density < eps ∧
--         (∀ y ∈ closedBall (0 : BaseModel) r,
--           dist ((intrinsicChartCoefficient b.tensor b.density seedPoint y,
--             fderiv ℝ (intrinsicChartCoefficient b.tensor b.density seedPoint) y) : CoefficientFirstJet BaseModel)
--             (roundCoefficientJet y) < delta) ∧
--         ∃ K' : Set Base, IsCompact K' ∧ K ⊆ K' ∧ K' ⊆ seedSpherePatch r ∧
--           (∀ x ∉ K', ∀ v w : AmbientBase, ⟪(x:AmbientBase),v⟫=0 → ⟪(x:AmbientBase),w⟫=0 →
--             b.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)=⟪v,w⟫) ∧
--           (∀ x ∉ K', b.density x=1) ∧
--           (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density u p y =
--             lam*u ((extChartAt (𝓡 4) p).symm y)) ∧
--           (∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
--             (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density v p y =
--               lam*v ((extChartAt (𝓡 4) p).symm y)) → ∃ c : ℝ, v=c • u)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Geometry.CoefficientDerivative`, `OAI.Yau.Geometry.CoefficientPoint`, `OAI.Yau.Geometry.clmAdd`, `OAI.Yau.Geometry.clmModule` and `OAI.Yau.Geometry.clmTopology` (definitions bundle `OAIQ237Ny000` of this split); `OAI.Yau.Target.AmbientBase`, `OAI.Yau.Target.BaseModel`, `OAI.Yau.Target.SphereCotangent`, `OAI.Yau.Target.intrinsicRoundPerturbationLocalInst3`, `OAI.Yau.Target.intrinsicRoundPerturbationLocalInst4`, `OAI.Yau.Target.seedPoint`, `OAI.Yau.Target.seedSpherePatch` and `OAI.Yau.Target.sphereCovectorRestriction` (definitions bundle `OAIQ237Ny001` of this split); `OAI.Yau.Target.SphereEnergyData`, `OAI.Yau.Target.intrinsicChartCoefficient` and `OAI.Yau.Target.roundCoefficientJet` (definitions bundle `OAIQ237Ny002` of this split); `OAI.Yau.Target.intrinsicWeightedChartOperator` and `OAI.Yau.Target.sphereCoefficientDistance` (definitions bundle `OAIQ237Ny004` of this split); `OAI.Yau.Target.Base` (the published bundle `Def_YauCounterexample`).
--
--   **Used by.** The proof of `OAI.Yau.Target.intrinsic_one_step` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Charts/SphereSimplicityInNeighborhood.lean (declaration OAI.Yau.Target.sphere_simplicity_in_comparison_neighborhood)

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
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Pow
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
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Harmonic.Basic
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finsupp.Weight
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
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
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
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.IsUniformGroup.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Topology.UniformSpace.UniformConvergence
import Mathlib.Topology.UniformSpace.UniformConvergenceTopology
import Definitions.Def_YauCounterexample
import Definitions.Def_OAIQ237Ny004

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Yau.Target
open Manifold Yau.Geometry Set Metric
open scoped ContDiff RealInnerProductSpace
noncomputable section
attribute [local instance] clmTopology clmAdd clmModule
attribute [local instance] intrinsicRoundPerturbationLocalInst3 intrinsicRoundPerturbationLocalInst4 intrinsicRoundPerturbationLocalInst5 intrinsicRoundPerturbationLocalInst6 intrinsicRoundPerturbationLocalInst7 intrinsicRoundPerturbationLocalInst8 intrinsicRoundPerturbationLocalInst9 intrinsicRoundPerturbationLocalInst10 intrinsicRoundPerturbationLocalInst11 intrinsicRoundPerturbationLocalInst12 intrinsicRoundPerturbationLocalInst13 intrinsicRoundPerturbationLocalInst14 intrinsicRoundPerturbationLocalInst15 intrinsicRoundPerturbationLocalInst16 intrinsicRoundPerturbationLocalInst17 intrinsicRoundPerturbationLocalInst18

theorem sphere_simplicity_in_comparison_neighborhood
    (d : SphereEnergyData) (hd : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ d.density)
    {r delta : ℝ} (hr : 0 < r)
    (hclose : ∀ y ∈ closedBall (0 : BaseModel) r,
      dist ((intrinsicChartCoefficient d.tensor d.density seedPoint y,
        fderiv ℝ (intrinsicChartCoefficient d.tensor d.density seedPoint) y) : CoefficientFirstJet BaseModel)
        (roundCoefficientJet y) < delta)
    (K : Set Base) (hK : IsCompact K) (hKP : K ⊆ seedSpherePatch r)
    (hA : ∀ x ∉ K, ∀ v w : AmbientBase, ⟪(x:AmbientBase),v⟫=0 → ⟪(x:AmbientBase),w⟫=0 →
      d.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)=⟪v,w⟫)
    (hrho : ∀ x ∉ K, d.density x=1)
    (u : Base → ℝ) (hu : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ u) (hu0 : u ≠ 0)
    (lam : ℝ) (hlam : 0 < lam)
    (he : ∀ p y, -intrinsicWeightedChartOperator d.tensor d.density u p y =
      lam*u ((extChartAt (𝓡 4) p).symm y))
    (P : Finset Base) (J : ℕ) (eps : ℝ) (heps : 0 < eps) :
    ∃ (b : SphereEnergyData) (_ : ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ b.density),
      sphereCoefficientDistance P J d.tensor d.density b.tensor b.density < eps ∧
      (∀ y ∈ closedBall (0 : BaseModel) r,
        dist ((intrinsicChartCoefficient b.tensor b.density seedPoint y,
          fderiv ℝ (intrinsicChartCoefficient b.tensor b.density seedPoint) y) : CoefficientFirstJet BaseModel)
          (roundCoefficientJet y) < delta) ∧
      ∃ K' : Set Base, IsCompact K' ∧ K ⊆ K' ∧ K' ⊆ seedSpherePatch r ∧
        (∀ x ∉ K', ∀ v w : AmbientBase, ⟪(x:AmbientBase),v⟫=0 → ⟪(x:AmbientBase),w⟫=0 →
          b.tensor x (sphereCovectorRestriction x v) (sphereCovectorRestriction x w)=⟪v,w⟫) ∧
        (∀ x ∉ K', b.density x=1) ∧
        (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density u p y =
          lam*u ((extChartAt (𝓡 4) p).symm y)) ∧
        (∀ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v →
          (∀ p y, -intrinsicWeightedChartOperator b.tensor b.density v p y =
            lam*v ((extChartAt (𝓡 4) p).symm y)) → ∃ c : ℝ, v=c • u) := by
  sorry

end
end Yau.Target

end OAI
end
