-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_rowTrunc_error
-- name    : OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.rowTrunc_error
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:07:10.168467+00:00
-- url     : https://prove2.me/theorems/c15ac46f-ac3c-45ea-b3c9-c9bf897254ae
-- title:
--   Window-truncated Fourier series of a periodised chirp converge uniformly at rate $O(1/T)$
-- statement:
--   Let $g:\mathbb{R}\to\mathbb{C}$ and write $\varphi_{t,u}(x)=e^{2\pi i(tx^2/2-ux)}$ for real $t,u$. For real $t$ the periodised chirp $\Gamma_t:\mathbb{R}/\mathbb{Z}\to\mathbb{C}$ is given by $\Gamma_t(x\bmod 1)=g(x)\,\varphi_{t,0}(x)$ for $-\tfrac12<x\le\tfrac12$. For real $T,\beta$ let $W_{T,\beta}=\{w\in\mathbb{Z}:|w|\le T|\beta|/2\}$ and define the truncated row
--   $$
--   R_{T,\beta}(z)=\sum_{w\in W_{T,\beta}}\Bigl(\int_{\mathbb{R}}g(x)\,\varphi_{T\beta,w}(x)\,dx\Bigr)e^{2\pi i wz},\qquad z\in\mathbb{R}/\mathbb{Z}.
--   $$
--
--   Assume that $g$ is infinitely differentiable with compact support, that $0\le\alpha<\tfrac12$ and the closed support of $g$ is contained in $[-\alpha,\alpha]$, and that $\beta\ne0$. Then there is a constant $C\ge0$ such that for every real $T\ge1$ and every $z\in\mathbb{R}/\mathbb{Z}$,
--   $$
--   \bigl|R_{T,\beta}(z)-\Gamma_{T\beta}(z)\bigr|\le\frac{C}{T}.
--   $$
--
--   The coefficients in $R_{T,\beta}$ are exactly the Fourier coefficients of $\Gamma_{T\beta}$, so $R_{T,\beta}$ is the partial sum of the Fourier series of the chirp over the window $W_{T,\beta}$. The theorem says that this trigonometric polynomial, with about $T|\beta|$ frequencies, approximates the chirp uniformly on the circle with error $O(1/T)$ as the curvature scale $T$ grows with $\beta$ fixed. It is the one-dimensional ingredient for replacing products of chirps by trigonometric polynomials in the Fourier-spreading construction.
--
--   **Formalization Note** $R_{T,\beta}$ is `rowTrunc g T β`, $\Gamma_t$ is `circleChirp g t`, and $W_{T,\beta}$ is `box T β`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/QuadraticTail.lean#L419-L437

import Mathlib
import Definitions.Def_AsymptoticallyMinimalLittlewood
import Definitions.Def_OAI_Analysis_Littlewood_Gaussian
import Definitions.Def_OAI_Analysis_Littlewood_Rounding
import Definitions.Def_OAI_Analysis_Littlewood_BinaryPacket
import Definitions.Def_OAI_Analysis_Littlewood_QuadraticTail

open OAI OAI.AsymptoticallyMinimalLittlewood OAI.AsymptoticallyMinimalLittlewood.QuadraticTail
universe uI uZ
open MeasureTheory Filter Topology Complex
open scoped BigOperators ContDiff

theorem OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.rowTrunc_error {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {α : ℝ} (hα0 : 0≤α) (hα : α<1/2)
    (hs : tsupport g ⊆ Set.Icc (-α) α) {β : ℝ} (hβ : β ≠ 0) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, 1≤T → ∀ z : UnitAddCircle,
      ‖rowTrunc g T β z-circleChirp g (T*β) z‖ ≤ C/T := by sorry
