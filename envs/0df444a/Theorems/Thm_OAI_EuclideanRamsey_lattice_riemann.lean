-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_lattice_riemann
-- name    : OAI.EuclideanRamsey.lattice_riemann
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:08:07.565287+00:00
-- url     : https://prove2.me/theorems/e2a03bdc-c29a-438b-93b6-585a3f13a9e9
-- title:
--   Riemann sums on the lattices $\tfrac1n\mathbb{Z}^k$ of a continuous compactly supported function converge to its integral
-- statement:
--   Let $k\in\mathbb{N}$ and let $f:\mathbb{R}^k\to\mathbb{R}$ be continuous with compact support. For $n\ge1$ and $\gamma\in\mathbb{Z}^k$ write $\gamma/n=(\gamma_1/n,\dots,\gamma_k/n)$. Then
--
--   $$
--   \lim_{n\to\infty}\frac{1}{n^k}\sum_{\gamma\in\mathbb{Z}^k}f\Big(\frac{\gamma}{n}\Big)\;=\;\int_{\mathbb{R}^k}f(x)\,dx,
--   $$
--
--   where $n$ runs through the natural numbers and the integral is with respect to Lebesgue measure. For each $n\ge1$ only finitely many terms of the sum are nonzero.
--
--   This is the convergence of Riemann sums on the refining grids $\tfrac1n\mathbb{Z}^k$, each of whose cells has volume $n^{-k}$. It allows integral inequalities for smooth bumps to be transferred to finite lattice sums at a sufficiently fine scale.
--
--   **Formalization Note** The sum is a `tsum` over `Fin k → ℤ`, the sample point is `latticeSample n γ`, and the limit is a `Tendsto` along `atTop`. For $n=0$ the sample point is $0$ by Lean's convention $x/0=0$; this single term does not affect the limit.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/Discretization.lean#L168-L188

import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization

open OAI OAI.EuclideanRamsey
universe uDomain uIndex
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open MeasureTheory
open scoped BigOperators
open scoped BigOperators
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter

theorem OAI.EuclideanRamsey.lattice_riemann {k : ℕ} {f : (Fin k → ℝ) → ℝ}
    (hf : Continuous f) (hfc : HasCompactSupport f) :
    Tendsto (fun n : ℕ => (∑' γ : Fin k → ℤ, f (latticeSample n γ))/(n:ℝ)^k)
      atTop (𝓝 (∫ x, f x)) := by sorry
