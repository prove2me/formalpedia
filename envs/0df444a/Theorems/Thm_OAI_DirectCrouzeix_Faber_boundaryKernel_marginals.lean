-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Faber_boundaryKernel_marginals
-- name    : OAI.DirectCrouzeix.Faber.boundaryKernel_marginals
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:46:37.010684+00:00
-- url     : https://prove2.me/theorems/62fdb412-4c8f-4ca0-931f-23988c5b2e1d
-- title:
--   Both marginals of the boundary kernel $1+2\,\operatorname{Re}\kappa(t,s)$ equal $1$
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
--   which is well defined since $|\overline{e(t)}|=1<R$. Let $P(t,s)=1+2\operatorname{Re}\kappa(t,s)$, a real-valued kernel on $\mathbb{T}\times\mathbb{T}$. Then
--   $$
--   \int_{\mathbb{T}}P(t,s)\,dt=1\quad\text{for every }s\in\mathbb{T},\qquad\int_{\mathbb{T}}P(t,s)\,ds=1\quad\text{for every }t\in\mathbb{T}.
--   $$
--
--   Thus $P$ has both marginals equal to $1$, so the integral operators it defines in either variable fix the constant functions. When $P$ is in addition nonnegative, it is a doubly stochastic kernel, and the corresponding averaging operator is a contraction on $L^2(\mathbb{T})$; this is how the upper bound with weights $1$ and $2$ for the boundary energy of Faber expansions is obtained.
--
--   **Formalization Note** $P$ is `boundaryKernel c g t s` and $\kappa$ is `boundaryCorrection c g t s`, with $\overline{e(t)}$ written as `(unitPoint t)⁻¹` and `unitPoint t = fourier 1 t`; $K$ is `correction c g` and $H$ is `chordDenominator c g`. The measure is `haarAddCircle` on `AddCircle (1:ℝ)`, a probability measure. No nonnegativity of $P$ and no separate assumption $c\neq0$ are made.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/BoundaryKernel.lean#L191-L211

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

theorem OAI.DirectCrouzeix.Faber.boundaryKernel_marginals {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0) :
    (∀ s, ∫ t, boundaryKernel c g t s ∂angularMeasure = 1) ∧
      (∀ t, ∫ s, boundaryKernel c g t s ∂angularMeasure = 1) := by sorry
