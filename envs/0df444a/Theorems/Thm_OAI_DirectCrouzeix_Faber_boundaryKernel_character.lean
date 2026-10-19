-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Faber_boundaryKernel_character
-- name    : OAI.DirectCrouzeix.Faber.boundaryKernel_character
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:49:02.04896+00:00
-- url     : https://prove2.me/theorems/e04ca613-1b99-46e4-8c13-483898515f60
-- title:
--   The boundary kernel sends the character $e^{2\pi i k t}$ to the boundary coefficient $B_k$
-- statement:
--   Let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ carry its Haar probability measure $dt$, write $\zeta_t=e^{2\pi i t}$ for $t\in\mathbb{T}$, and for an integrable $f:\mathbb{T}\to\mathbb{C}$ let $\hat f(n)=\int_{\mathbb{T}}e^{-2\pi i n t}f(t)\,dt$ $(n\in\mathbb{Z})$ be its Fourier coefficients.
--
--   Fix $R>1$, a function $g:\mathbb{C}\to\mathbb{C}$ that is analytic on the open disc $D_R=\{u\in\mathbb{C}:|u|<R\}$, and $c\in\mathbb{C}$. For $u,v\in D_R$ consider the chord averages
--   $$
--   D(u,v)=\int_0^1 g'\big((1-\tau)u+\tau v\big)\,d\tau,\qquad D_1(u,v)=\int_0^1(1-\tau)\,g''\big((1-\tau)u+\tau v\big)\,d\tau
--   $$
--   (so $D(u,v)=\frac{g(u)-g(v)}{u-v}$ for $u\neq v$ and $D(u,u)=g'(u)$), the chord denominator $H(u,v)=c-uv\,D(u,v)$, and the correction
--   $$
--   Q(u,v)=\frac{uv\,\big(D(u,v)+u\,D_1(u,v)\big)}{H(u,v)}.
--   $$
--   On $\mathbb{T}\times\mathbb{T}$ define the boundary correction $S(t,s)=Q(\zeta_t^{-1},\zeta_s^{-1})$, the real boundary kernel $K(t,s)=1+2\operatorname{Re}S(t,s)$, and, for $k\in\mathbb{N}$, the boundary coefficient
--   $$
--   B_k(s)=\int_{\mathbb{T}}e^{2\pi i k t}\,S(t,s)\,dt,
--   $$
--   that is, the Fourier coefficient of index $-k$ of $t\mapsto S(t,s)$.
--
--   **Theorem.** Assume $H(u,v)\neq0$ for all $u,v\in D_R$. Then for every integer $k\ge1$ and every $s\in\mathbb{T}$,
--   $$
--   \int_{\mathbb{T}}K(t,s)\,e^{2\pi i k t}\,dt=B_k(s).
--   $$
--
--   Here $\Phi(\zeta)=c\zeta+g(1/\zeta)$ parametrizes the closed curve $s\mapsto\Phi(\zeta_s)$, and elsewhere in the development $B_k(s)$ is identified with the defect $F_k(\Phi(\zeta_s))-\zeta_s^k$ of the $k$-th Faber polynomial $F_k$ of $\Phi$ on that curve. The identity says that the integral operator with the real kernel $K$ maps every positive character $e^{2\pi i k t}$, $k\ge1$, to this defect. Combined with the fact that $K$ has unit marginals, it represents the whole Faber remainder $\sum_k B_k(s)C_k$ as a $K$-average of the trigonometric polynomial $\sum_{k\ge1}e^{2\pi i k t}C_k$, which is what a Markov-kernel $L^2$ contraction estimate needs.
--
--   **Formalization Note** $\mathbb{T}$ is `Angle = AddCircle (1:ℝ)` with `angularMeasure = haarAddCircle`, $\zeta_t$ is `unitPoint t = fourier 1 t`, and $e^{2\pi i k t}$ is `fourier k t`. The objects $D$, $D_1$, $H$, $Q$, $S$, $K$, $B_k$ are `divided`, `dividedLeft`, `chordDenominator`, `correction`, `boundaryCorrection`, `boundaryKernel` and `boundaryCoefficient`; the chord averages are integrals over the parameter interval $[0,1]$ and use Lean's `deriv`, which is the complex derivative on $D_R$. The index $k$ is a natural number with $k\neq0$, and $K(t,s)$ is real and is coerced to $\mathbb{C}$ in the integral.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/BoundaryKernel.lean#L217-L246

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

theorem OAI.DirectCrouzeix.Faber.boundaryKernel_character {R : ℝ} (hR : 1 < R) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (ball 0 R)) {c : ℂ}
    (hH : ∀ u ∈ ball 0 R, ∀ v ∈ ball 0 R, chordDenominator c g u v ≠ 0)
    (k : ℕ) (hk : k ≠ 0) (s : Angle) :
    (∫ t, (boundaryKernel c g t s : ℂ) * fourier (k:ℤ) t ∂angularMeasure) =
      boundaryCoefficient c g k s := by sorry
