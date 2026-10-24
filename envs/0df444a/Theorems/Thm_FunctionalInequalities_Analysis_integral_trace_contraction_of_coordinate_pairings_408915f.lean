-- Prove2me | Theorems.Thm_FunctionalInequalities_Analysis_integral_trace_contraction_of_coordinate_pairings_408915f
-- name    : FunctionalInequalities.Analysis.integral_trace_contraction_of_coordinate_pairings_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T13:26:20.141321+00:00
-- url     : https://prove2.me/theorems/aefe5c6b-4373-43db-b147-ce460468f495
-- title:
--   Coordinate Trace Contraction Identity
-- statement:
--   This private auxiliary statement performs a finite trace contraction of coordinatewise integral identities.
--
--   Let d,n,m be natural numbers. On $E=\operatorname{EuclideanSpace}\,\mathbb R\,(\operatorname{Fin} d)$, let B be an n-by-n matrix; let H and E be matrix fields; let T and J be m-indexed matrix fields; let ρ and ψ be scalar fields; and let dψₐ be scalar coordinate derivatives. Assume the five families of coordinate expressions appearing in the theorem are integrable, including the pairings involving J, T, H, E, B, ρ, ψ, and dψ. Assume also that for every l,k,i,j,
--
--   $$\int ρ\sum_a J_{a,ij}\bigl(ψT_{a,lk}+dψ_aH_{lk}\bigr)\,d\mu
--   =-\int ρE_{ij}ψH_{lk}\,d\mu.$$
--
--   Then the contracted flux identity holds:
--
--   $$\int ρ\sum_a 2\operatorname{tr}(BHBJ_a)\,dψ_a\,d\mu
--   =-\int ρ\left(2\operatorname{tr}(BHBE)+\sum_a2\operatorname{tr}(BT_aBJ_a)\right)ψ\,d\mu.$$
--
--   This is a private finite-sum and trace-algebra support lemma used by the public weak trace contraction theorem.
--
--   **Formalization Note** All integrals are with respect to the explicitly supplied measure μ; no analytic interpretation of the fields as Hessians or derivatives is assumed.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Analysis/Matrix/WeakTrace.lean#L48-L179 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Analysis.Matrix.WeakTrace`, declaration `_private.FunctionalInequalities.Analysis.Matrix.WeakTrace.0.FunctionalInequalities.Analysis.integral_trace_contraction_of_coordinate_pairings`; the repository is private at upload time).

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
section FixedTestFiniteContraction
open MeasureTheory Matrix
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis

theorem FunctionalInequalities.Analysis.integral_trace_contraction_of_coordinate_pairings_408915f {d n m : ℕ}
    (mu : Measure (EuclideanSpace ℝ (Fin d)))
    (B : Matrix (Fin n) (Fin n) ℝ)
    (H E : EuclideanSpace ℝ (Fin d) → Matrix (Fin n) (Fin n) ℝ)
    (T J : EuclideanSpace ℝ (Fin d) → Fin m → Matrix (Fin n) (Fin n) ℝ)
    (rho psi : EuclideanSpace ℝ (Fin d) → ℝ)
    (dpsi : Fin m → EuclideanSpace ℝ (Fin d) → ℝ)
    (hPair : ∀ l k i j : Fin n, Integrable (fun x => rho x *
      (∑ a : Fin m, J x a i j * (psi x * T x a l k + dpsi a x * H x l k))) mu)
    (hForce : ∀ l k i j : Fin n, Integrable
      (fun x => rho x * E x i j * (psi x * H x l k)) mu)
    (hTensor : ∀ a : Fin m, Integrable
      (fun x => rho x * psi x * (2 * (B * T x a * B * J x a).trace)) mu)
    (hFlux : ∀ a : Fin m, Integrable
      (fun x => rho x * dpsi a x * (2 * (B * H x * B * J x a).trace)) mu)
    (hTraceForce : Integrable
      (fun x => rho x * psi x * (2 * (B * H x * B * E x).trace)) mu)
    (hTest : ∀ l k i j : Fin n,
      (∫ x, rho x * (∑ a : Fin m, J x a i j *
        (psi x * T x a l k + dpsi a x * H x l k)) ∂mu) =
      -(∫ x, rho x * E x i j * (psi x * H x l k) ∂mu)) :
    (∫ x, rho x * (∑ a : Fin m, (2 * (B * H x * B * J x a).trace) * dpsi a x) ∂mu) =
      -(∫ x, rho x *
        (2 * (B * H x * B * E x).trace +
          ∑ a : Fin m, 2 * (B * T x a * B * J x a).trace) * psi x ∂mu) := by sorry
