-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_stencil_weighted_riemann
-- name    : OAI.EuclideanRamsey.stencil_weighted_riemann
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T02:12:54.674559+00:00
-- url     : https://prove2.me/theorems/7201c4f6-768f-4d61-be14-ade39e4950bc
-- title:
--   Lattice Riemann sums of the negative part of a second-order difference stencil converge to the continuum integral
-- statement:
--   Let $k,d\in\mathbb N$, let $S$ be a finite index set, and let $q_\gamma\in\mathbb R$ (weights) and $v_\gamma\in\mathbb R^k$ (shift vectors), $\gamma\in S$, satisfy the moment conditions
--   $$\sum_{\gamma\in S}q_\gamma=0,\qquad\sum_{\gamma\in S}q_\gamma\,v_{\gamma,j}=0,\qquad\sum_{\gamma\in S}q_\gamma\,v_{\gamma,j}\,v_{\gamma,l}=C_{jl}\qquad(1\le j,l\le k)$$
--   for a real $k\times k$ matrix $C$. Let $U$ be a real $d\times k$ matrix and let $b:\mathbb R^k\to\mathbb R$ be a $C^\infty$ function with compact support. Write
--   $$\mathcal D_Cb(x)=\frac12\sum_{j,l=1}^kC_{jl}\,\partial_j\partial_l b(x),\qquad W_U(x)=\sum_{a=1}^d\Bigl(\sum_{j=1}^kU_{aj}x_j\Bigr)^2=|Ux|^2\qquad(x\in\mathbb R^k).$$
--   Then, as $n\to\infty$ through the natural numbers,
--   $$\frac1{n^k}\sum_{\delta\in\mathbb Z^k}\max\Bigl(-n^2\sum_{\gamma\in S}q_\gamma\,b\Bigl(\frac{\delta}{n}-\frac{v_\gamma}{n}\Bigr),\,0\Bigr)\,W_U\Bigl(\frac{\delta}{n}\Bigr)\ \longrightarrow\ \int_{\mathbb R^k}\max\bigl(-\mathcal D_Cb(x),\,0\bigr)\,W_U(x)\,dx,$$
--   where the integral is taken with respect to Lebesgue measure on $\mathbb R^k$.
--
--   The quantity $n^2\sum_{\gamma}q_\gamma\,b(x-v_\gamma/n)$ is a finite-difference stencil applied to $b$ at mesh $1/n$; the moment conditions make it an approximation of the constant-coefficient second-order operator $\mathcal D_C$. The theorem says that the lattice Riemann sums of the negative part of this stencil, weighted by $|Ux|^2$, converge to the corresponding continuum integral. It is the discretization step that transfers a smooth bump with small weighted negative part to a lattice function with the same property.
--
--   **Formalization Note** The lattice point $\delta/n$ is `latticeSample n δ` (coordinates $\delta_j/n$), $\mathcal D_Cb$ is `stencilDifferential C b` (defined through the second iterated Fréchet derivative of $b$), $W_U$ is `gradientWeight U`, and smoothness is `ContDiff ℝ (⊤ : ℕ∞) b`. The sum over $\mathbb Z^k$ is a `tsum`; for $n\ge1$ it has only finitely many nonzero terms because $b$ has compact support.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/StencilConvolution.lean#L107-L201

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
open MeasureTheory Filter
open scoped BigOperators Topology

theorem OAI.EuclideanRamsey.stencil_weighted_riemann {ι : Type uIndex} {k d : ℕ} (S : Finset ι)
    (q : ι → ℝ) (v : ι → (Fin k → ℝ)) (C : Matrix (Fin k) (Fin k) ℝ)
    (U : Matrix (Fin d) (Fin k) ℝ)
    (hzero : ∑ γ ∈ S,q γ = 0) (hfirst : ∀ j,∑ γ ∈ S,q γ*v γ j = 0)
    (hsecond : ∀ j l,∑ γ ∈ S,q γ*v γ j*v γ l = C j l)
    {b : (Fin k → ℝ) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbc : HasCompactSupport b) :
    Tendsto (fun n : ℕ => (∑' δ : Fin k → ℤ,
      max (-((n:ℝ)^2*∑ γ ∈ S,q γ*b (latticeSample n δ+(-(n:ℝ)⁻¹) • v γ))) 0 *
        gradientWeight U (latticeSample n δ))/(n:ℝ)^k) atTop
      (𝓝 (∫ x,max (-stencilDifferential C b x) 0*gradientWeight U x)) := by sorry
