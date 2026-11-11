-- Prove2me | Theorems.Thm_OAI_Yau_Target_sphere_normalized_global_limit
-- name    : OAI.Yau.Target.sphere_normalized_global_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T00:34:04.385558+00:00
-- url     : https://prove2.me/theorems/4599c647-ff0d-4ed3-b0b1-ebbacbecdeee
-- title:
--   OAI.Yau.Target.sphere_normalized_global_limit: intermediate lemma from OpenAI, Power-law violations of Yau's nodal upper bound
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Yau.Target.yau_nodal_set_upper_bound_counterexample`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Power-law violations of Yau's nodal upper bound*, OpenAI Math Release, September 23, 2026, result family 350, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Yau.Target.sphere_normalized_global_limit` of [lean/OAI/Geometry/NodalSets/Charts/SphereNormalizedGlobalLimit.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Charts/SphereNormalizedGlobalLimit.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Yau.Target`, with `open Manifold Yau.Analysis Yau.Geometry Set Metric Filter`, `open scoped Topology ContDiff`):
--
--   ```lean
--   theorem sphere_normalized_global_limit (A : T → IntrinsicTensor) (rho : T → Base → ℝ)
--       (hA : ∀ t, IntrinsicTensorSmooth (A t))
--       (hs : ∀ t p v w, A t p v w = A t p w v) (hp : ∀ t p v, v ≠ 0 → 0 < A t p v v)
--       (hr : ∀ t, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (rho t)) (hrp : ∀ t p, 0 < rho t p)
--       (hrjoint : Continuous (fun z : T × Base ↦ rho z.1 z.2)) (lam : ℝ)
--       (hCjoint : ∀ p i j ds, Continuous (fun z : T × Yau.Jets.Coord ↦
--         partialJet (fun x ↦ intrinsicDivergencePrincipal (A z.1) p x i j) ds z.2))
--       (hVjoint : ∀ p ds, Continuous (fun z : T × Yau.Jets.Coord ↦
--         partialJet (intrinsicDivergencePotential (rho z.1) lam p) ds z.2))
--       (t : ℕ → T) (t0 : T) (ht : Tendsto t atTop (𝓝 t0)) (w : ℕ → Base → ℝ) (hw : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (w j))
--       (he : ∀ j q z, -intrinsicWeightedChartOperator (A (t j)) (rho (t j)) (w j) q z =
--         lam*w j ((extChartAt (𝓡 4) q).symm z))
--       (hn : ∀ j, sphereWeightedPairing (rho (t j)) (w j) (w j)=1)
--       (u : Base → ℝ) (hu : Continuous u)
--       (ho : ∀ j, sphereWeightedPairing (rho (t j)) (w j) u=0) :
--       ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
--         (∀ p z, -intrinsicWeightedChartOperator (A t0) (rho t0) v p z =
--           lam*v ((extChartAt (𝓡 4) p).symm z)) ∧
--         sphereWeightedPairing (rho t0) v v=1 ∧ sphereWeightedPairing (rho t0) v u=0 ∧
--         ∃ nu : ℕ → ℕ, StrictMono nu ∧ TendstoUniformly (fun j ↦ w (nu j)) v atTop ∧
--           (∀ p ds (Q : Set Yau.Jets.Coord), IsCompact Q →
--             TendstoUniformlyOn (fun j ↦ partialJet (w (nu j) ∘ sphereChartCoordMap p) ds)
--               (partialJet (v ∘ sphereChartCoordMap p) ds) atTop Q) ∧
--           (∀ p n (Q : Set Yau.Jets.Coord), IsCompact Q →
--             TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (w (nu j) ∘ sphereChartCoordMap p))
--               (iteratedFDeriv ℝ n (v ∘ sphereChartCoordMap p)) atTop Q)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Yau.Analysis.partialJet` and `OAI.Yau.Jets.Coord` (definitions bundle `OAIQ237Ny000` of this split); `OAI.Yau.Target.BaseModel`, `OAI.Yau.Target.IntrinsicTensor`, `OAI.Yau.Target.IntrinsicTensorSmooth` and `OAI.Yau.Target.SphereCotangent` (definitions bundle `OAIQ237Ny001` of this split); `OAI.Yau.Target.sphereChartCoordMap` and `OAI.Yau.Target.sphereWeightedPairing` (definitions bundle `OAIQ237Ny002` of this split); `OAI.Yau.Target.intrinsicDivergencePotential`, `OAI.Yau.Target.intrinsicDivergencePrincipal` and `OAI.Yau.Target.intrinsicWeightedChartOperator` (definitions bundle `OAIQ237Ny004` of this split); `OAI.Yau.Target.Base` (the published bundle `Def_YauCounterexample`).
--
--   **Used by.** The proof of `OAI.Yau.Target.sphere_affine_kernel_implies_simplicity` of this split imports it.
-- source:
--   OpenAI, Power-law violations of Yau's nodal upper bound, OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 350; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Power-law-violations-of-Yaus-nodal-upper-bound-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Geometry/NodalSets/Charts/SphereNormalizedGlobalLimit.lean (declaration OAI.Yau.Target.sphere_normalized_global_limit)

import Mathlib
import Mathlib.Algebra.MvPolynomial.PDeriv
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
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Real
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
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
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
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Ring.Basic
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Sequences
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
open Manifold Yau.Analysis Yau.Geometry Set Metric Filter
open scoped Topology ContDiff
noncomputable section
variable {T : Type*} [TopologicalSpace T] [CompactSpace T]

theorem sphere_normalized_global_limit (A : T → IntrinsicTensor) (rho : T → Base → ℝ)
    (hA : ∀ t, IntrinsicTensorSmooth (A t))
    (hs : ∀ t p v w, A t p v w = A t p w v) (hp : ∀ t p v, v ≠ 0 → 0 < A t p v v)
    (hr : ∀ t, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (rho t)) (hrp : ∀ t p, 0 < rho t p)
    (hrjoint : Continuous (fun z : T × Base ↦ rho z.1 z.2)) (lam : ℝ)
    (hCjoint : ∀ p i j ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (fun x ↦ intrinsicDivergencePrincipal (A z.1) p x i j) ds z.2))
    (hVjoint : ∀ p ds, Continuous (fun z : T × Yau.Jets.Coord ↦
      partialJet (intrinsicDivergencePotential (rho z.1) lam p) ds z.2))
    (t : ℕ → T) (t0 : T) (ht : Tendsto t atTop (𝓝 t0)) (w : ℕ → Base → ℝ) (hw : ∀ j, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ (w j))
    (he : ∀ j q z, -intrinsicWeightedChartOperator (A (t j)) (rho (t j)) (w j) q z =
      lam*w j ((extChartAt (𝓡 4) q).symm z))
    (hn : ∀ j, sphereWeightedPairing (rho (t j)) (w j) (w j)=1)
    (u : Base → ℝ) (hu : Continuous u)
    (ho : ∀ j, sphereWeightedPairing (rho (t j)) (w j) u=0) :
    ∃ v : Base → ℝ, ContMDiff (𝓡 4) 𝓘(ℝ,ℝ) ∞ v ∧ v ≠ 0 ∧
      (∀ p z, -intrinsicWeightedChartOperator (A t0) (rho t0) v p z =
        lam*v ((extChartAt (𝓡 4) p).symm z)) ∧
      sphereWeightedPairing (rho t0) v v=1 ∧ sphereWeightedPairing (rho t0) v u=0 ∧
      ∃ nu : ℕ → ℕ, StrictMono nu ∧ TendstoUniformly (fun j ↦ w (nu j)) v atTop ∧
        (∀ p ds (Q : Set Yau.Jets.Coord), IsCompact Q →
          TendstoUniformlyOn (fun j ↦ partialJet (w (nu j) ∘ sphereChartCoordMap p) ds)
            (partialJet (v ∘ sphereChartCoordMap p) ds) atTop Q) ∧
        (∀ p n (Q : Set Yau.Jets.Coord), IsCompact Q →
          TendstoUniformlyOn (fun j ↦ iteratedFDeriv ℝ n (w (nu j) ∘ sphereChartCoordMap p))
            (iteratedFDeriv ℝ n (v ∘ sphereChartCoordMap p)) atTop Q) := by
  sorry

end
end Yau.Target

end OAI
end
