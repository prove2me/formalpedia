-- Prove2me | Theorems.Thm_OAI_DirectCrouzeix_Faber_correction_identity
-- name    : OAI.DirectCrouzeix.Faber.correction_identity
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:41:32.162848+00:00
-- url     : https://prove2.me/theorems/01d49ea7-cae3-4eaf-902a-2bc83e63b5b8
-- title:
--   Closed form of the Faber correction kernel $K(u,v)$
-- statement:
--   Let $g:\mathbb{C}\to\mathbb{C}$ and $c\in\mathbb{C}$. For $u,v\in\mathbb{C}$ define the integrals along the segment from $u$ to $v$
--   $$
--   D(u,v)=\int_0^1 g'\big((1-t)u+tv\big)\,dt,\qquad D_L(u,v)=\int_0^1(1-t)\,g''\big((1-t)u+tv\big)\,dt,
--   $$
--   the denominator $H(u,v)=c-uv\,D(u,v)$, the correction kernel $K(u,v)=uv\,\big(D(u,v)+u\,D_L(u,v)\big)/H(u,v)$, and the exterior map $\psi(\zeta)=c\,\zeta+g(1/\zeta)$. Let $s\subseteq\mathbb{C}$ be open and convex and let $g$ be complex analytic at every point of $s$. If $u,v\in s$, $v\neq0$, $u\neq v$ and $H(u,v)\neq0$, then
--   $$
--   K(u,v)=\frac{c-u^2g'(u)}{c+u\,\big(g(u)-\psi(1/v)\big)}-\frac{1}{1-u/v}.
--   $$
--   Under these hypotheses both denominators on the right are nonzero; in fact $c+u\,(g(u)-\psi(1/v))=H(u,v)\,(v-u)/v$.
--
--   The first term on the right is the classical generating function $\frac{c-u^2g'(u)}{c+u\,(g(u)-z)}=\sum_{k\ge0}\Phi_k(z)\,u^k$ of the Faber polynomials $\Phi_k$ of $\psi$, evaluated at $z=\psi(1/v)$; the second term is the geometric series $\sum_{k\ge0}(u/v)^k$. The identity therefore exhibits $K(\cdot,v)$ as a generating function of the differences $\Phi_k(\psi(1/v))-v^{-k}$, which is how the Faber polynomials along the image of a circle are compared with pure powers.
--
--   **Formalization Note** $D$, $D_L$, $H$, $K$ and $\psi$ are `divided g`, `dividedLeft g`, `chordDenominator c g`, `correction c g` and `exterior c g`; derivatives are Lean's `deriv`. All divisions in the statement have nonzero denominators under the hypotheses, so Lean's convention $x/0=0$ plays no role. No assumption $c\neq0$ is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/DirectCrouzeix/DividedDifferences.lean#L140-L156

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

open OAI OAI.DirectCrouzeix OAI.DirectCrouzeix.Faber
open scoped Matrix Matrix.Norms.L2Operator Kronecker
open MeasureTheory Set Filter Metric
open scoped Topology Interval ENNReal NNReal ComplexConjugate

theorem OAI.DirectCrouzeix.Faber.correction_identity {s : Set ℂ} (hs : IsOpen s) (hconv : Convex ℝ s)
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g s) (c : ℂ) {u v : ℂ}
    (hu : u ∈ s) (hv : v ∈ s) (hv0 : v ≠ 0) (huv : u ≠ v)
    (hH : chordDenominator c g u v ≠ 0) :
    correction c g u v = (c-u^2*deriv g u)/(c+u*(g u-exterior c g v⁻¹)) - (1-u/v)⁻¹ := by sorry
