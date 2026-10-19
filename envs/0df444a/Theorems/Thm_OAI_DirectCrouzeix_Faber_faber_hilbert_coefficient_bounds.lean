-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Faber_faber_hilbert_coefficient_bounds
-- name    : OAI.DirectCrouzeix.Faber.faber_hilbert_coefficient_bounds
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:51:54.031238+00:00
-- url     : https://prove2.me/theorems/854697be-0859-4e8b-bb35-7f27462f5775
-- title:
--   Two-sided energy bounds for Faber series with Hilbert-space coefficients on the boundary curve
-- statement:
--   Let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ carry its Haar probability measure $dt$ and write $\zeta_t=e^{2\pi i t}$. Fix $R>1$, a function $g:\mathbb{C}\to\mathbb{C}$ analytic on the open disc $D_R=\{u\in\mathbb{C}:|u|<R\}$, and $c\in\mathbb{C}$ with $c\neq0$. Put $\Phi(\zeta)=c\zeta+g(1/\zeta)$, so that $t\mapsto\Phi(\zeta_t)$ is a closed curve.
--
--   *Faber polynomials.* With $L(u)=\big(c+u\,g(u)\big)^{-1}$, $W(u)=u\,L(u)$ and $V(u)=\big(c-u^2g'(u)\big)L(u)$, all analytic near $u=0$, the $k$-th Faber polynomial is
--   $$
--   F_k(z)=\sum_{j=0}^{k}a_{k,j}\,z^j,\qquad a_{k,j}=\frac{1}{k!}\,\frac{d^k}{du^k}\Big|_{u=0}\Big(V(u)\,W(u)^j\Big).
--   $$
--   Equivalently $\sum_{k\ge0}F_k(z)\,u^k=\dfrac{c-u^2g'(u)}{c+u\,(g(u)-z)}$ near $u=0$; these are the Faber polynomials of $\Phi$.
--
--   *Boundary kernel.* For $u,v\in D_R$ let $D(u,v)=\int_0^1 g'\big((1-\tau)u+\tau v\big)\,d\tau$, $D_1(u,v)=\int_0^1(1-\tau)\,g''\big((1-\tau)u+\tau v\big)\,d\tau$, $H(u,v)=c-uv\,D(u,v)$ and $Q(u,v)=uv\,\big(D(u,v)+u\,D_1(u,v)\big)/H(u,v)$, and on $\mathbb{T}\times\mathbb{T}$ let $K(t,s)=1+2\operatorname{Re}Q(\zeta_t^{-1},\zeta_s^{-1})$.
--
--   **Theorem.** Assume that $H(u,v)\neq0$ for all $u,v\in D_R$ and that $K(t,s)\ge0$ for all $t,s\in\mathbb{T}$. Let $E$ be a complex Hilbert space, $N\in\mathbb{N}$ and $C_0,\dots,C_{N-1}\in E$. Then
--   $$
--   \sum_{k=0}^{N-1}\|C_k\|^2\;\le\;\int_{\mathbb{T}}\Big\|\sum_{k=0}^{N-1}F_k\big(\Phi(\zeta_t)\big)\,C_k\Big\|^2dt\;\le\;\sum_{k=0}^{N-1}w_k\,\|C_k\|^2,\qquad w_0=1,\ \ w_k=2\ (k\ge1).
--   $$
--
--   So, as soon as the boundary kernel is nonnegative, the Faber polynomials evaluated on the curve $\Phi(\zeta_t)$ behave like a Riesz system in $L^2(\mathbb{T};E)$: the boundary energy of every finite Faber expansion with Hilbert-space coefficients lies between the squared $\ell^2$ norm of the coefficients and twice that norm, the factor $2$ affecting only the nonconstant terms. In the development the positivity of $K$ is derived from a supporting-line (convexity-type) condition on the boundary curve, and the estimate is applied with matrix coefficients viewed as Hilbert–Schmidt vectors.
--
--   **Formalization Note** $F_k$ is `faberBasis c g k`, whose coefficients are given by `taylorCoeff` ($k!^{-1}$ times Lean's `iteratedDeriv k` at $0$); $\Phi(\zeta_t)$ is `boundary c g t`, the Faber expansion is `faberBoundarySeries c g C t` with `C : Fin N → E`, $K$ is `boundaryKernel c g`, and $H$ is `chordDenominator c g`. The upper bound is written with the weights `if k = 0 then 1 else 2`. The hypothesis $c\neq0$ is in fact also implied by $H(0,0)=c\neq0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/FaberEnergy.lean#L77-L110

import Mathlib
import Definitions.Def_DirectCrouzeix
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PositiveBlocks
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Resolvent
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialCalculus
import Definitions.Def_OAI_Analysis_DirectCrouzeix_HilbertSchmidt
import Definitions.Def_OAI_Analysis_DirectCrouzeix_SingularPairs
import Definitions.Def_OAI_Analysis_DirectCrouzeix_Sharpness
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CircleFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_PolynomialEnergy
import Definitions.Def_OAI_Analysis_DirectCrouzeix_CompactIntegrals
import Definitions.Def_OAI_Analysis_DirectCrouzeix_DividedDifferences
import Definitions.Def_OAI_Analysis_DirectCrouzeix_TaylorFourier
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberPolynomials
import Definitions.Def_OAI_Analysis_DirectCrouzeix_BoundaryKernel
import Definitions.Def_OAI_Analysis_DirectCrouzeix_KernelContraction
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberEnergy

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
universe u_128 u_129
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
variable {E : Type u_128} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem OAI.DirectCrouzeix.Faber.faber_hilbert_coefficient_bounds {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ} (hc : c ≠ 0)
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (hpositive : ∀ t s, 0 ≤ boundaryKernel c g t s)
    {N : ℕ} (C : Fin N → E) :
    (∑ k, ‖C k‖^2 ≤ ∫ t, ‖faberBoundarySeries c g C t‖^2 ∂angularMeasure) ∧
      ((∫ t, ‖faberBoundarySeries c g C t‖^2 ∂angularMeasure) ≤
        ∑ k : Fin N, (if (k:ℕ) = 0 then 1 else 2)*‖C k‖^2) := by sorry
