-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_stencil_taylor_uniform
-- name    : OAI.EuclideanRamsey.stencil_taylor_uniform
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:11:41.790169+00:00
-- url     : https://prove2.me/theorems/666d820c-6e5c-46a2-8367-5f089bf30214
-- title:
--   Finite-difference stencils with matched moments approximate $\tfrac12\sum C_{jl}\partial_j\partial_l$ uniformly at rate $O(1/t)$
-- statement:
--   Let $k\in\mathbb{N}$, let $S$ be a finite index set, and for each $\gamma\in S$ let $q_\gamma\in\mathbb{R}$ and $v_\gamma=(v_{\gamma,1},\dots,v_{\gamma,k})\in\mathbb{R}^k$. Let $C$ be a real $k\times k$ matrix, and assume that the weighted configuration has vanishing mass, vanishing first moments and second-moment matrix $C$:
--   $$
--   \sum_{\gamma\in S}q_\gamma=0,\qquad\sum_{\gamma\in S}q_\gamma\,v_{\gamma,j}=0,\qquad\sum_{\gamma\in S}q_\gamma\,v_{\gamma,j}\,v_{\gamma,l}=C_{jl}\qquad(1\le j,l\le k).
--   $$
--   Let $b:\mathbb{R}^k\to\mathbb{R}$ be $C^\infty$ with compact support, and let $L_Cb(x)=\tfrac12\sum_{j,l}C_{jl}\,\partial_j\partial_lb(x)$. Then there is a constant $K\ge0$ such that for every $t>0$ and every $x\in\mathbb{R}^k$
--
--   $$
--   \Big|\,t^2\sum_{\gamma\in S}q_\gamma\,b\big(x-t^{-1}v_\gamma\big)\;-\;L_Cb(x)\Big|\;\le\;\frac Kt .
--   $$
--
--   Thus the finite-difference operator $b\mapsto t^2\sum_\gamma q_\gamma\,b(\cdot-v_\gamma/t)$, whose stencil has the moments of a second-order operator, converges to $L_Cb$ uniformly on $\mathbb{R}^k$ at rate $O(1/t)$ as $t\to\infty$. With $t=n$ and integer stencil points $v_\gamma\in\mathbb{Z}^k$, this compares the convolution of a lattice measure with the samples of $b$ on $\tfrac1n\mathbb{Z}^k$ to the differential expression $L_Cb$.
--
--   **Formalization Note** $L_Cb(x)$ is `stencilDifferential C b x = (1/2) * ∑ j, ∑ l, C j l * iteratedFDeriv ℝ 2 b x ![Pi.single j 1, Pi.single l 1]`, and the shifted point is written `x + (-t⁻¹) • v γ`. $C$ is not assumed symmetric (the second-moment hypothesis forces it to be). The constant $K$ depends on the stencil and on $b$, but not on $t$ or $x$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/StencilConvolution.lean#L26-L84

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
universe uIndex
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
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped BigOperators

theorem OAI.EuclideanRamsey.stencil_taylor_uniform {ι : Type uIndex} {k : ℕ} (S : Finset ι)
    (q : ι → ℝ) (v : ι → (Fin k → ℝ)) (C : Matrix (Fin k) (Fin k) ℝ)
    (hzero : ∑ γ ∈ S,q γ = 0) (hfirst : ∀ j,∑ γ ∈ S,q γ*v γ j = 0)
    (hsecond : ∀ j l,∑ γ ∈ S,q γ*v γ j*v γ l = C j l)
    {b : (Fin k → ℝ) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbc : HasCompactSupport b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t : ℝ), 0 < t → ∀ x,
      |t^2*(∑ γ ∈ S,q γ*b (x+(-t⁻¹) • v γ))-stencilDifferential C b x| ≤ K/t := by sorry
