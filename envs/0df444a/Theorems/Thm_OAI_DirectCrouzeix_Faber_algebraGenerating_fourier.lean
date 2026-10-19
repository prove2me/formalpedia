-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Faber_algebraGenerating_fourier
-- name    : OAI.DirectCrouzeix.Faber.algebraGenerating_fourier
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:53:52.186264+00:00
-- url     : https://prove2.me/theorems/43c567ea-a1b4-48e8-992a-5ac952b9ff3d
-- title:
--   Faber polynomials of a Banach-algebra element as Fourier coefficients on the unit circle
-- statement:
--   Let $\mathcal{A}$ be a complex Banach algebra with unit $\mathbf 1$, let $\mathbb{T}=\mathbb{R}/\mathbb{Z}$ carry its Haar probability measure $dt$, and for a continuous $h:\mathbb{T}\to\mathcal{A}$ write $\hat h(n)=\int_{\mathbb{T}}e^{-2\pi i n t}\,h(t)\,dt$ $(n\in\mathbb{Z})$. Fix $R>1$, $c\in\mathbb{C}$ with $c\neq0$, and $g:\mathbb{C}\to\mathbb{C}$ analytic on the open disc $D_R=\{|u|<R\}$. With $L(u)=(c+u\,g(u))^{-1}$, $W(u)=u\,L(u)$ and $V(u)=(c-u^2g'(u))L(u)$, let
--   $$
--   F_k(z)=\sum_{j=0}^{k}a_{k,j}z^j,\qquad a_{k,j}=\frac{1}{k!}\frac{d^k}{du^k}\Big|_{u=0}\big(V(u)W(u)^j\big)
--   $$
--   be the Faber polynomials, and for $A\in\mathcal{A}$ let $G_A(u)=\big(c-u^2g'(u)\big)\big((c+u\,g(u))\mathbf 1-uA\big)^{-1}$.
--
--   Let $A\in\mathcal{A}$ and assume that $(c+u\,g(u))\mathbf 1-uA$ is invertible in $\mathcal{A}$ for every $u$ with $|u|\le1$. Put $h(t)=G_A(e^{-2\pi i t})$. Then $h$ is continuous and
--   $$
--   \hat h(-k)=\int_{\mathbb{T}}e^{2\pi i k t}\,G_A(e^{-2\pi i t})\,dt=F_k(A)\quad(k=0,1,2,\dots),\qquad \hat h(k)=0\quad(k=1,2,\dots).
--   $$
--   Precisely, the theorem asserts the conjunction of three statements:
--
--   1. $h:\mathbb{T}\to\mathcal{A}$ is continuous;
--   2. $\hat h(-k)=F_k(A)$ for every $k\in\mathbb{N}$;
--   3. $\hat h(k)=0$ for every integer $k>0$.
--
--   For $0<|u|\le1$ the bracket equals $u\,(\Phi(1/u)\mathbf 1-A)$ with $\Phi(\zeta)=c\zeta+g(1/\zeta)$, so the hypothesis says exactly that the spectrum of $A$ avoids $\{\Phi(\zeta):|\zeta|\ge1\}$. On the circle $G_A(1/\zeta)=\zeta\,\Phi'(\zeta)\,(\Phi(\zeta)\mathbf 1-A)^{-1}$, hence statement 2 is the Faber operator formula $F_k(A)=\frac{1}{2\pi i}\oint_{|\zeta|=1}\zeta^k\,\Phi'(\zeta)\,(\Phi(\zeta)\mathbf 1-A)^{-1}\,d\zeta$, while statement 3 says that the boundary function has no positive frequencies. These facts express Faber polynomials of a matrix or operator through integrals over the curve $\Phi(e^{2\pi it})$.
--
--   **Formalization Note** $G_A$ is `algebraGenerating c g A`, built with `Ring.inverse` of `algebraDenominator c g A u`; under the invertibility hypothesis this is the true inverse at the points used. The point $e^{-2\pi i t}$ is `(unitPoint t)⁻¹`, $\hat h$ is Mathlib's `fourierCoeff` on `AddCircle (1:ℝ)` with `haarAddCircle`, $F_k(A)$ is `Polynomial.aeval A (faberBasis c g k)`, and $g'$ is Lean's `deriv g`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/FaberCalculus.lean#L139-L163

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
import Definitions.Def_OAI_Analysis_DirectCrouzeix_FaberCalculus

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
universe u_129 u_130
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate
variable {𝔄 : Type u_129} [NormedRing 𝔄] [NormedAlgebra ℂ 𝔄] [CompleteSpace 𝔄]

theorem OAI.DirectCrouzeix.Faber.algebraGenerating_fourier {R : ℝ} (hR : 1 < R) {c : ℂ} (hc : c ≠ 0)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g (ball 0 R)) (A : 𝔄)
    (hunit : ∀ u ∈ closedBall 0 1, IsUnit (algebraDenominator c g A u)) :
    (Continuous (fun t : Angle => algebraGenerating c g A (unitPoint t)⁻¹)) ∧
    (∀ k : ℕ, fourierCoeff (fun t : Angle => algebraGenerating c g A (unitPoint t)⁻¹)
      (-(k:ℤ)) = Polynomial.aeval A (faberBasis c g k)) ∧
    (∀ k : ℤ, 0 < k → fourierCoeff (fun t : Angle => algebraGenerating c g A (unitPoint t)⁻¹) k = 0) := by sorry
