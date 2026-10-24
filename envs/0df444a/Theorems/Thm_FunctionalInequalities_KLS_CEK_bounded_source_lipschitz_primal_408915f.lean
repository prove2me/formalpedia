-- Prove2me | Theorems.Thm_FunctionalInequalities_KLS_CEK_bounded_source_lipschitz_primal_408915f
-- name    : FunctionalInequalities.KLS.CEK.bounded_source_lipschitz_primal_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:22:34.297821+00:00
-- url     : https://prove2.me/theorems/03d175cf-dcc8-4d8d-974a-19085b8ddda8
-- title:
--   Normalized Lipschitz Primal
-- statement:
--   This is a normalized primal construction for a bounded isotropic source law.
--
--   Let $E$ be a finite-dimensional real inner-product space with Borel measurable structure, let $\mu$ be an isotropic probability measure, and let $L\in[0,\infty)$. Assume $\|y\|\le L$ for $\mu$-almost every $y$. Then there exist $q:E\to\overline{\mathbb{R}}$, $a\in E$, $m\in\mathbb{R}$, and $\psi:E\to\mathbb{R}$ satisfying all of the finite-conjugate conclusions: $q$ is convex, lower semicontinuous, potential-integrable, finite only inside $\overline{B}(0,L)$, has a minimum $q(a)=m$, and $m\le q$. Its conjugate is everywhere finite and obeys
--
--   $$
--   q^*(x)\le L\|x\|-m,
--   \qquad q^*(x)=\psi(x).
--   $$
--
--   In addition,
--
--   $$
--   \operatorname{mass}_{dx}(q^*)=1,
--   $$
--
--   $\psi$ is convex and $L$-Lipschitz, and $\psi$ is continuous. Moreover,
--
--   $$
--   \int e^{-\psi(x)}\,dx=1,
--   $$
--
--   and the corresponding weighted measure is a probability measure. Every potential-integrable competitor $f$ satisfies
--
--   $$
--   I_{dx,\mu}(f)\le I_{dx,\mu}(q).
--   $$
--
--   This is a weak normalized convex-Lipschitz primal; it does not assert a gradient pushforward or smoothness beyond the stated continuity.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/KLS/CEK/BoundedPrimal.lean#L280-L321 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.KLS.CEK.BoundedPrimal`, declaration `FunctionalInequalities.KLS.CEK.bounded_source_lipschitz_primal`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Affine
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_BoundedConjugate
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_RadialExtension
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_Isotropic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_AffineSupport
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Covariance_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Affine.Isometry
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Abs
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Group.LIntegral
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.MeasureTheory.Measure.Tilted
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Probability.Moments.CovarianceBilin
import Mathlib.Tactic.NoncommRing
import Mathlib.Topology.Bases
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IsLUB
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Sequences

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.CEK
end FunctionalInequalities.KLS.CEK
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.CEK
open MeasureTheory Set Metric
open scoped ENNReal Topology RealInnerProductSpace
open FunctionalInequalities
open FunctionalInequalities.Analysis
open FunctionalInequalities.KLS
open FunctionalInequalities.Probability
open FunctionalInequalities.Probability.MomentMeasure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem FunctionalInequalities.KLS.CEK.bounded_source_lipschitz_primal_408915f
    (μ : ProbabilityMeasure E) (hμ : KLS.Isotropic μ) (L : NNReal)
    (hL : ∀ᵐ y ∂(μ : Measure E), ‖y‖ ≤ (L : ℝ)) :
    ∃ (q : E → EReal) (a : E) (m : ℝ) (ψ : E → ℝ),
      ConvexPotential q ∧
      LowerSemicontinuous q ∧
      PotentialIntegrable q (μ : Measure E) ∧
      (∀ y, q y ≠ ⊤ → y ∈ closedBall (0 : E) (L : ℝ)) ∧
      a ∈ closedBall (0 : E) (L : ℝ) ∧
      q a = (m : EReal) ∧
      (∀ y, (m : EReal) ≤ q y) ∧
      (∀ x, legendre q x ≠ ⊤ ∧ legendre q x ≠ ⊥) ∧
      (∀ x, legendre q x ≤ (((L : ℝ) * ‖x‖ - m : ℝ) : EReal)) ∧
      ψ = (fun x => (legendre q x).toReal) ∧
      (∀ x, legendre q x = (ψ x : EReal)) ∧
      mass (volume : Measure E) (legendre q) = 1 ∧
      ConvexOn ℝ (univ : Set E) ψ ∧
      LipschitzWith L ψ ∧
      Continuous ψ ∧
      Integrable (fun x => Real.exp (-ψ x)) (volume : Measure E) ∧
      (∫ x, Real.exp (-ψ x) ∂(volume : Measure E)) = 1 ∧
      IsProbabilityMeasure
        (weightedMeasure (volume : Measure E) (fun x => (ψ x : EReal))) ∧
      ∀ f : E → EReal, PotentialIntegrable f (μ : Measure E) →
        variationalFunctional (volume : Measure E) (μ : Measure E) f ≤
          variationalFunctional (volume : Measure E) (μ : Measure E) q := by sorry
