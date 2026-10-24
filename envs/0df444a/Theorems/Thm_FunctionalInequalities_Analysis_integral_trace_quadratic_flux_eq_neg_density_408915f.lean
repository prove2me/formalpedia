-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_trace_quadratic_flux_eq_neg_density_408915f
-- name    : FunctionalInequalities.Analysis.integral_trace_quadratic_flux_eq_neg_density_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:26:20.299854+00:00
-- url     : https://prove2.me/theorems/0b6d57ae-c24e-45bf-8015-51f2e9f765bd
-- title:
--   Weak Trace Quadratic Flux Identity
-- statement:
--   This formalizes the weak counterpart of Lemma 2.4, equations (2.8) and (2.10), of Letwin (arXiv:2607.24164v1), cited in relation to Theorem 2.5.
--
--   Let n be a natural number and work on $E=\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin} n)$. Let B be a constant matrix, H,R,E be matrix fields, T a field of matrix-valued tensor slices, and ρ a continuous scalar weight. Assume
--
--   1. every entry of H is in $L^\infty$ with respect to volume;
--   2. every entry of T is locally in $L^2$ on compact sets;
--   3. every entry of $\sum_bR_{ba}T_b$ is locally in $L^2$ on compact sets;
--   4. every entry of E is locally integrable; and
--   5. for every compactly supported C¹ test ψ and every l,k,i,j, the stated coordinate weak identity holds:
--      $$\int ρ\sum_a\left(\sum_bR_{ba}T_{b,ij}\right)\left(ψT_{a,lk}+D_{e_a}ψ\,H_{lk}\right)\,dx
--      =-\int ρE_{ij}ψH_{lk}\,dx.$$
--
--   Define
--
--   $$a(x,i)=2\operatorname{tr}(BH(x)B T(x,i)),$$
--
--   and
--
--   $$g(x)=2\operatorname{tr}(BH(x)BE(x))+2\sum_{i,j}R(x,i,j)\operatorname{tr}(BT(x,i)BT(x,j)).$$
--
--   Then g is locally integrable. For every compactly supported C¹ test ψ, the relevant flux terms and density term are integrable, and
--
--   $$\int ρ\sum_j\left(\sum_iR_{ij}a_i\right)D_{e_j}ψ\,dx
--   =-\int ρgψ\,dx.$$
--
--   This is the public weak trace-contraction theorem for rough finite-dimensional matrix fields; it does not itself assume a Hessian, potential, or source interpretation.
-- source:
--   Source: Letwin, The KLS constant is O(log^(1/4) n) (arXiv:2607.24164v1), Theorem 2.5. Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/WeakTrace.lean#L321-L479 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.WeakTrace`, declaration `FunctionalInequalities.Analysis.integral_trace_quadratic_flux_eq_neg_density`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Cutoff_SmoothBall
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Lipschitz_Gradient
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Norm
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.SpecificCodomains.Pi
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NoncommRing
import Mathlib.Tactic.Positivity
import Mathlib.Topology.MetricSpace.Lipschitz

noncomputable section
section WeakTraceIdentity
open MeasureTheory Filter Set Matrix
open scoped ContDiff Topology
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
set_option maxHeartbeats 1000000

theorem FunctionalInequalities.Analysis.integral_trace_quadratic_flux_eq_neg_density_408915f {n : ℕ}
    (B : Matrix (Fin n) (Fin n) ℝ)
    (H R E : EuclideanSpace ℝ (Fin n) → Matrix (Fin n) (Fin n) ℝ)
    (T : EuclideanSpace ℝ (Fin n) → Fin n → Matrix (Fin n) (Fin n) ℝ)
    (ρ : EuclideanSpace ℝ (Fin n) → ℝ)
    (hρ : Continuous ρ)
    (hH : ∀ i j : Fin n, MemLp (fun x => H x i j) (⊤ : ENNReal)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hT : ∀ a i j : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => T x a i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hJ : ∀ i j a : Fin n, ∀ S : Set (EuclideanSpace ℝ (Fin n)), IsCompact S →
      MemLp (fun x => ∑ b : Fin n, R x b a * T x b i j) 2
        ((volume : Measure (EuclideanSpace ℝ (Fin n))).restrict S))
    (hE : ∀ i j : Fin n, LocallyIntegrable (fun x => E x i j)
      (volume : Measure (EuclideanSpace ℝ (Fin n))))
    (hTest : ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ → ∀ l k i j : Fin n,
      (∫ x, ρ x * (∑ a : Fin n, (∑ b : Fin n, R x b a * T x b i j) *
        (ψ x * T x a l k +
          fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ a) * H x l k))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, ρ x * E x i j * (ψ x * H x l k)
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n))))) :
    let a := fun x i => 2 * (B * H x * B * T x i).trace
    let g := fun x => 2 * (B * H x * B * E x).trace +
      2 * ∑ i : Fin n, ∑ j : Fin n, R x i j * (B * T x i * B * T x j).trace
    LocallyIntegrable g (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
    ∀ ψ : EuclideanSpace ℝ (Fin n) → ℝ,
      ContDiff ℝ 1 ψ → HasCompactSupport ψ →
      Integrable (fun x => ρ x * g x * ψ x)
        (volume : Measure (EuclideanSpace ℝ (Fin n))) ∧
      (∀ j : Fin n, Integrable (fun x => ρ x *
        (∑ i : Fin n, R x i j * a x i) *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
        (volume : Measure (EuclideanSpace ℝ (Fin n)))) ∧
      (∫ x, ρ x * (∑ j : Fin n, (∑ i : Fin n, R x i j * a x i) *
        fderiv ℝ ψ x (EuclideanSpace.basisFun (Fin n) ℝ j))
        ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) =
      -(∫ x, ρ x * g x * ψ x ∂(volume : Measure (EuclideanSpace ℝ (Fin n)))) := by sorry
