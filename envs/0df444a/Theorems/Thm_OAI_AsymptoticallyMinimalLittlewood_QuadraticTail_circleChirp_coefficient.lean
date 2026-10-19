-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_circleChirp_coefficient
-- name    : OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.circleChirp_coefficient
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:02:49.438055+00:00
-- url     : https://prove2.me/theorems/5d2be727-747a-446a-875c-1682ab533ae0
-- title:
--   Fourier coefficients of a periodised chirp are chirp integrals over the real line
-- statement:
--   Identify the circle $\mathbb{R}/\mathbb{Z}$ with the fundamental interval $(-\tfrac12,\tfrac12]$ and equip it with its Haar probability measure. For a function $g:\mathbb{R}\to\mathbb{C}$ and a real number $t$, the periodised chirp $\Gamma_{g,t}:\mathbb{R}/\mathbb{Z}\to\mathbb{C}$ is given on the fundamental interval by $\Gamma_{g,t}(x \bmod 1)=g(x)\,e^{2\pi i\,t x^2/2}$ for $-\tfrac12<x\le\tfrac12$. The $w$-th Fourier coefficient of a function $F$ on the circle is $\widehat F(w)=\int_{\mathbb{R}/\mathbb{Z}}F(z)\,e^{-2\pi i wz}\,dz$.
--
--   Let $\alpha<\tfrac12$ and suppose that the closed support of $g$ is contained in $[-\alpha,\alpha]$. Then for every real $t$ and every integer $w$,
--
--   $$
--   \widehat{\Gamma_{g,t}}(w)=\int_{\mathbb{R}} g(x)\,e^{2\pi i\,(t x^2/2-wx)}\,dx .
--   $$
--
--   Because the support of $g$ fits inside one period, periodisation loses nothing, and the Fourier coefficients of the periodised chirp are exactly the chirp integrals over the real line with linear frequency $w$. This dictionary lets Fourier-series facts on the circle, such as Parseval's identity or the pointwise convergence of absolutely summable Fourier series, be applied to the integrals $\int g(x)e^{2\pi i(tx^2/2-wx)}\,dx$.
--
--   **Formalization Note** $\Gamma_{g,t}$ is `circleChirp g t`, defined with `AddCircle.liftIoc 1 (-1/2)`, and the coefficient is Mathlib's `fourierCoeff` on `UnitAddCircle`. No regularity of $g$ is assumed; both sides are Bochner integrals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/QuadraticTail.lean#L292-L314

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

theorem OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.circleChirp_coefficient {g : ℝ → ℂ} {α : ℝ}
    (hα : α<1/2) (hs : tsupport g ⊆ Set.Icc (-α) α) (t : ℝ) (w : ℤ) :
    fourierCoeff (circleChirp g t) w = ∫ x : ℝ, g x*phase t w x := by sorry
