-- Prove2me | Theorems.Thm_ModernOnlineLearning_FTRL_lemma_7_49
-- name    : ModernOnlineLearning.FTRL.lemma_7_49
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T02:37:01.584988+00:00
-- url     : https://prove2.me/theorems/a2870c7e-811d-4d3e-8dbe-929bddca0b29
-- title:
--   Lemma 7.49, p. 131 — stability of regularized linear minimizers
-- statement:
--   Let $\psi$ be $\lambda$-strongly convex on a nonempty, closed and convex feasible set $V$, where $\lambda>0$. For dual vectors $\theta^{(1)}$ and $\theta^{(2)}$, let $x^{(j)}$ minimize $\psi(z)+\theta^{(j)}(z)$ over $V$. Then
--   $$\|x^{(1)}-x^{(2)}\|\le\frac{\|\theta^{(1)}-\theta^{(2)}\|_*}{\lambda}.$$
--   The lemma controls how much a regularized linear prediction can change when its linear term changes.
--
--   **Formalization Note** The two minimizers are supplied rather than selected by a choice operator. Dual vectors are continuous linear functionals, and their operator norm is $\|\cdot\|_*$.
-- source:
--   Orabona, arXiv:1912.13213v10, Lemma 7.49, p. 131

import Mathlib
import Definitions.Def_ModernOnlineLearning_FTRL_Defs

set_option autoImplicit false

namespace ModernOnlineLearning.FTRL

/-- Orabona, Lemma 7.49, p. 131: sensitivity of a regularized linear minimizer. -/
theorem lemma_7_49
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (V : Set E) (hVclosed : IsClosed V) (hVconvex : Convex ℝ V)
    (hVnonempty : V.Nonempty) (ψ : E → ℝ)
    (lam : ℝ) (hlam : 0 < lam) (hStrong : StrongConvexOn V lam ψ)
    (θ₁ θ₂ : E →L[ℝ] ℝ) (x₁ x₂ : E)
    (hx₁ : IsMinimizerOn V (fun z => ψ z + θ₁ z) x₁)
    (hx₂ : IsMinimizerOn V (fun z => ψ z + θ₂ z) x₂) :
    ‖x₁ - x₂‖ ≤ (1 / lam) * ‖θ₁ - θ₂‖ := by sorry

end ModernOnlineLearning.FTRL
