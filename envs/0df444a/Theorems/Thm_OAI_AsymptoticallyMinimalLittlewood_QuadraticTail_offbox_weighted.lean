-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_offbox_weighted
-- name    : OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.offbox_weighted
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:05:29.266692+00:00
-- url     : https://prove2.me/theorems/e2c7ba93-20bc-4378-acad-67a830f91d7e
-- title:
--   Off-window chirp integrals are bounded by $C\,T^{-n}(1+|w|)^{-2}$
-- statement:
--   Let $g:\mathbb{R}\to\mathbb{C}$ be infinitely differentiable with compact support, let $0\le\alpha<\tfrac12$ be such that the closed support of $g$ is contained in $[-\alpha,\alpha]$, let $\beta\ne0$ be real and let $n\ge0$ be an integer. For real $T$ let $W_{T,\beta}=\{w\in\mathbb{Z}:\ |w|\le T|\beta|/2\}$ be the frequency window, and let $\lambda(w)=(1+|w|)^{-2}$. Then there is a constant $C\ge0$ such that for every real $T\ge1$ and every integer $w\notin W_{T,\beta}$,
--
--   $$
--   \Bigl|\int_{\mathbb{R}} g(x)\,e^{2\pi i\,(T\beta x^2/2-wx)}\,dx\Bigr|\le\frac{C}{T^{n}}\,\lambda(w).
--   $$
--
--   For integer frequencies outside the window (where the stationary point $w/(T\beta)$ of the phase lies outside $[-\tfrac12,\tfrac12]$), the chirp integrals, which are the Fourier coefficients of the periodised chirp $g(x)e^{\pi iT\beta x^2}$, are thus simultaneously small in the scale $T$, to any prescribed polynomial order, and dominated by a summable function of $w$. With $n=1$ this yields $O(1/T)$ bounds both for the discarded squared Fourier mass and for the uniform error of truncating the Fourier series to the window.
--
--   **Formalization Note** The window is `box T β`, the integer interval from $-\lfloor T|\beta|/2\rfloor$ to $\lfloor T|\beta|/2\rfloor$, which is the same set as $W_{T,\beta}$; the weight is `latticeWeight w`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/QuadraticTail.lean#L353-L379

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

theorem OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.offbox_weighted {g : ℝ → ℂ} (hg : HasCompactSupport g)
    (hgs : ContDiff ℝ ∞ g) {α : ℝ} (hα0 : 0≤α) (hα : α<1/2)
    (hs : tsupport g ⊆ Set.Icc (-α) α) {β : ℝ} (hβ : β ≠ 0) (n : ℕ) :
    ∃ C : ℝ, 0≤C ∧ ∀ T : ℝ, 1≤T → ∀ w : ℤ, w ∉ box T β →
      ‖∫ x : ℝ, g x*phase (T*β) w x‖ ≤ C / T^n * latticeWeight w := by sorry
