-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_lattice_riemann_perturb
-- name    : OAI.EuclideanRamsey.lattice_riemann_perturb
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:09:36.201643+00:00
-- url     : https://prove2.me/theorems/aab84bc7-baa6-467f-b389-dd9f3dbaacab
-- title:
--   Lattice Riemann sums of uniformly convergent perturbations $g_n\to f$ converge to $\int f$
-- statement:
--   Let $k\in\mathbb{N}$ and $R>0$, and let $B_R=\{x\in\mathbb{R}^k:\max_j|x_j|\le R\}$ be the closed ball of radius $R$ for the sup norm, i.e. the cube $[-R,R]^k$. Let $f:\mathbb{R}^k\to\mathbb{R}$ be continuous with compact support, let $(g_n)_{n\in\mathbb{N}}$ be a sequence of functions $g_n:\mathbb{R}^k\to\mathbb{R}$ (no regularity is assumed), and let $(\varepsilon_n)_{n\in\mathbb{N}}$ be a sequence of real numbers with $\varepsilon_n\to0$. Assume:
--
--   1. the support of $f$ and the support of every $g_n$ are contained in $B_R$;
--   2. $|g_n(x)-f(x)|\le\varepsilon_n$ for all $n\ge1$ and all $x\in\mathbb{R}^k$.
--
--   Then, writing $\gamma/n=(\gamma_1/n,\dots,\gamma_k/n)$,
--
--   $$
--   \lim_{n\to\infty}\frac1{n^k}\sum_{\gamma\in\mathbb{Z}^k}g_n\Big(\frac\gamma n\Big)\;=\;\int_{\mathbb{R}^k}f(x)\,dx,
--   $$
--
--   with the integral taken with respect to Lebesgue measure.
--
--   So the Riemann sum at scale $n$ may be taken of an $n$-dependent function $g_n$, as long as $g_n$ approaches $f$ uniformly and all supports stay in a fixed bounded set. This is used for finite-difference approximations $g_n$ of a differential expression, which converge to it uniformly at rate $O(1/n)$.
--
--   **Formalization Note** On `Fin k → ℝ` Lean uses the sup norm, so `Metric.closedBall 0 R` is the cube $[-R,R]^k$. The lattice sums are `tsum`s over `Fin k → ℤ` (finite sums for $n\ge1$), the sample point $\gamma/n$ is `latticeSample n γ`, and the limit is a `Tendsto` along `atTop`. The uniform bound is only required for $n\ge1$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/RationalConvolution.lean#L52-L79

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
universe uGroup uIndex
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open MeasureTheory Filter
open scoped BigOperators Pointwise Topology

theorem OAI.EuclideanRamsey.lattice_riemann_perturb {k : ℕ} (f : (Fin k → ℝ) → ℝ)
    (g : ℕ → (Fin k → ℝ) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    {R : ℝ} (hR : 0 < R)
    (hfs : Function.support f ⊆ Metric.closedBall 0 R)
    (hgs : ∀ n, Function.support (g n) ⊆ Metric.closedBall 0 R)
    (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0))
    (hbound : ∀ n, 1 ≤ n → ∀ x, |g n x-f x| ≤ ε n) :
    Tendsto (fun n : ℕ => (∑' γ : Fin k → ℤ, g n (latticeSample n γ))/(n:ℝ)^k)
      atTop (𝓝 (∫ x, f x)) := by sorry
