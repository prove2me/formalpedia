-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Faber_boundaryCoefficient_no_nonnegative
-- name    : OAI.DirectCrouzeix.Faber.boundaryCoefficient_no_nonnegative
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:46:00.395362+00:00
-- url     : https://prove2.me/theorems/48f69a66-5942-4030-a7d2-1b41b21b8a05
-- title:
--   The boundary Faber error terms have no Fourier modes of nonnegative frequency
-- statement:
--   Let $R>1$, let $g:\mathbb{C}\to\mathbb{C}$ be complex analytic on the disk $\mathbb{D}_R=\{u\in\mathbb{C}:|u|<R\}$, and let $c\in\mathbb{C}$. For $u,v\in\mathbb{C}$ put
--   $$
--   D(u,v)=\int_0^1g'\big((1-t)u+tv\big)\,dt,\qquad D_L(u,v)=\int_0^1(1-t)\,g''\big((1-t)u+tv\big)\,dt,\qquad H(u,v)=c-uv\,D(u,v),
--   $$
--   and let $K(u,v)=uv\,\big(D(u,v)+u\,D_L(u,v)\big)/H(u,v)$ be the correction kernel. Assume
--   $$
--   H(u,v)\neq0\qquad\text{for all }u,v\in\mathbb{D}_R
--   $$
--   (taking $u=v=0$ shows that this includes $c\neq0$). Let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ carry its normalized Haar measure, let $e(t)=e^{2\pi it}$ for $t\in\mathbb{T}$, and define the boundary kernel
--   $$
--   \kappa(t,s)=K\big(\overline{e(t)},\overline{e(s)}\big)\qquad(t,s\in\mathbb{T}),
--   $$
--   which is well defined since $|\overline{e(t)}|=1<R$. For $k\in\mathbb{N}$ and $s\in\mathbb{T}$ let
--   $$
--   \beta_k(s)=\int_{\mathbb{T}}e^{2\pi ikt}\,\kappa(t,s)\,dt
--   $$
--   be the $(-k)$-th Fourier coefficient of $t\mapsto\kappa(t,s)$. Then for every $k\in\mathbb{N}$ and every integer $j\ge0$,
--   $$
--   \widehat{\beta_k}(j)=\int_{\mathbb{T}}e^{-2\pi ijs}\,\beta_k(s)\,ds=0 .
--   $$
--
--   In the Faber analysis, $\beta_k$ is the boundary error term in $\Phi_k\big(\psi(e(s))\big)=e^{2\pi iks}+\beta_k(s)$, where $\psi(\zeta)=c\zeta+g(1/\zeta)$ and $\Phi_k$ are the Faber polynomials of $\psi$. The theorem says that every $\beta_k$ is anti-analytic with mean zero: it is orthogonal in $L^2(\mathbb{T})$ to $e^{2\pi ijs}$ for every $j\ge0$, so the main terms and the error terms of a Faber expansion on the boundary are orthogonal. This yields a Pythagorean splitting of the boundary energy of a Faber expansion into the squared norms of its coefficients plus the energy of the error terms, and hence the lower bound in the comparison between the two.
--
--   **Formalization Note** $\kappa$ and $\beta_k$ are `boundaryCorrection c g t s` and `boundaryCoefficient c g k s`, with $\overline{e(t)}$ written as `(unitPoint t)⁻¹` and `unitPoint t = fourier 1 t`; $K$ is `correction c g` and $H$ is `chordDenominator c g`. Fourier coefficients are Mathlib's `fourierCoeff` on `AddCircle (1:ℝ)` with `haarAddCircle`. There is no separate assumption $c\neq0$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/BoundaryKernel.lean#L149-L172

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

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
universe u_108 u_109 u_110 u_111 u_112 u_113 u_114 u_115 u_116
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate

theorem OAI.DirectCrouzeix.Faber.boundaryCoefficient_no_nonnegative {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (k : ℕ) (j : ℤ) (hj : 0 ≤ j) :
    fourierCoeff (boundaryCoefficient c g k) j = 0 := by sorry
