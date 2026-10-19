-- Prove2me | Theorems.Thm_OAI_AsymptoticallyMinimalLittlewood_QuadraticTail_offbox_decay
-- name    : OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.offbox_decay
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T05:01:23.719189+00:00
-- url     : https://prove2.me/theorems/64b6b81b-05b0-4a19-9db2-268d1eda7257
-- title:
--   Chirp integrals decay rapidly when the stationary point lies outside $[-\tfrac12,\tfrac12]$
-- statement:
--   Let $g:\mathbb{R}\to\mathbb{C}$ be infinitely differentiable with compact support, and let $\alpha$ be a real number with $0\le\alpha<\tfrac12$ such that the closed support of $g$ is contained in $[-\alpha,\alpha]$. Let $\beta\neq0$ be real and let $l\ge0$ be an integer. Then there is a constant $C\ge0$ such that for all real numbers $T$ and $w$ with $T>0$ and $|w|>T|\beta|/2$,
--
--   $$
--   (T+|w|)^{l}\,\Bigl|\int_{\mathbb{R}} g(x)\,e^{2\pi i\,(T\beta x^2/2-wx)}\,dx\Bigr|\le C .
--   $$
--
--   The phase $x\mapsto T\beta x^2/2-wx$ has its only stationary point at $x_0=w/(T\beta)$, and the condition $|w|>T|\beta|/2$ says exactly that $|x_0|>\tfrac12$: the stationary point lies outside $[-\tfrac12,\tfrac12]$, while the amplitude lives in $[-\alpha,\alpha]$. In this regime the chirp integral decays faster than any power of $T+|w|$, jointly in the curvature scale $T$ and the linear frequency $w$, with a constant depending only on $g,\alpha,\beta,l$. Specialised to integer $w$, this controls the Fourier coefficients of the periodised chirp $g(x)e^{\pi i T\beta x^2}$ outside the frequency window $|w|\le T|\beta|/2$.
--
--   **Formalization Note** The integrand is `g x * phase (T*β) w x`, where `phase t u x` is $e^{2\pi i(tx^2/2-ux)}$; here $w$ is an arbitrary real number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Littlewood/QuadraticTail.lean#L231-L267

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

theorem OAI.AsymptoticallyMinimalLittlewood.QuadraticTail.offbox_decay {g : ℝ → ℂ} (hg : HasCompactSupport g) (hgs : ContDiff ℝ ∞ g)
    {α β : ℝ} (hα : 0 ≤ α) (hα' : α < 1/2) (hβ : β ≠ 0)
    (hsupp : tsupport g ⊆ Set.Icc (-α) α) (l : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T w : ℝ, 0 < T → T*|β|/2 < |w| →
      (T+|w|)^l * ‖∫ x : ℝ, g x*phase (T*β) w x‖ ≤ C := by sorry
