-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_exists_penalized_maximum_with_comparison_408915f
-- name    : FunctionalInequalities.Analysis.exists_penalized_maximum_with_comparison_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:19:45.936556+00:00
-- url     : https://prove2.me/theorems/e0d2a112-28c9-46a1-a20a-f29d39d2ad95
-- title:
--   Penalized Maximum and Density Comparison
-- statement:
--   This is a weak-route supporting theorem for Letwin’s second-difference argument.
--
--   Let $u,F:\mathbb R^n\to\mathbb R$. Assume: $u$ is convex, globally Lipschitz, and has compact sublevel sets; $F$ is continuous; and for every open $G$, the Alexandrov identity
--   $$\operatorname{vol}(\partial u(G))=\int_G e^{F(x)}\,dx$$
--   holds. Let $u_k\in C^2$ and $F_k$ satisfy uniform approximation $|u_k-u|\le\delta_k$ with $\delta_k\to0$, local uniform convergence $F_k\to F$, positive-definite $\nabla^2u_k$, and $F_k\le\log\det\nabla^2u_k$. For every $h\in\mathbb R^n$ and $\eta>0$, there exists $x_0$ such that $\Delta_h^2u(x_0)-\eta u(x_0)$ is maximal and
--
--   $$F(x_0+h)+F(x_0-h)-2F(x_0)\le\eta n.$$
--
--   This is an auxiliary existence and comparison result, not a dimension-free bound.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Convex/Viscosity.lean#L1701-L1795 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Convex.Viscosity`, declaration `FunctionalInequalities.Analysis.exists_penalized_maximum_with_comparison`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_HessianOperator
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_AffineMaximum
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Alexandrov
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Proximal
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Subgradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Viscosity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Matrix_Positivity
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Operator_Coordinates
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_BrunnMinkowski
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_Line_BrunnMinkowski
import Mathlib
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.NormDet
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Positive
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Affine.Convex
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Isometric
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.EReal.Operations
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic

noncomputable section
open Set Metric Filter
open scoped RealInnerProductSpace Topology
open FunctionalInequalities.Probability.Stein
section LT17BMaximumWithComparison
open MeasureTheory Set Metric Filter
open scoped RealInnerProductSpace ENNReal Topology
open FunctionalInequalities.Probability.Stein
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
set_option maxHeartbeats 800000

theorem FunctionalInequalities.Analysis.exists_penalized_maximum_with_comparison_408915f {n : ℕ} {u F : EuclideanSpace ℝ (Fin n) → ℝ}
    (hconv : ConvexOn ℝ univ u) {L : NNReal} (hLip : LipschitzWith L u)
    (hcoer : ∀ R : ℝ, IsCompact {x | u x ≤ R}) (hF : Continuous F)
    (hMA : ∀ G : Set (EuclideanSpace ℝ (Fin n)), IsOpen G →
      (volume : Measure (EuclideanSpace ℝ (Fin n))) (subgradientImage u G) =
        ∫⁻ x in G, ENNReal.ofReal (Real.exp (F x)) ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))
    {uk Fk : ℕ → EuclideanSpace ℝ (Fin n) → ℝ} (huk : ∀ k, ContDiff ℝ 2 (uk k))
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (hclose : ∀ k x, |uk k x - u x| ≤ δ k)
    (hFk : TendstoLocallyUniformly Fk F atTop)
    (hpos : ∀ k x, (hessianMatrix (uk k) x).PosDef)
    (hlog : ∀ k x, Fk k x ≤ Real.log (hessianMatrix (uk k) x).det)
    (h : EuclideanSpace ℝ (Fin n)) {η : ℝ} (hη : 0 < η) :
    ∃ x₀ : EuclideanSpace ℝ (Fin n),
      (∀ y, u (y + h) + u (y - h) - 2 * u y - η * u y ≤
        u (x₀ + h) + u (x₀ - h) - 2 * u x₀ - η * u x₀) ∧
      F (x₀ + h) + F (x₀ - h) - 2 * F x₀ ≤ η * n := by sorry
