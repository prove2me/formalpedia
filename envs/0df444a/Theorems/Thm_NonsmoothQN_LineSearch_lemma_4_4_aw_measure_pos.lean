-- Prove2me | Theorems.Thm_NonsmoothQN_LineSearch_lemma_4_4_aw_measure_pos
-- name    : NonsmoothQN.LineSearch.lemma_4_4_aw_measure_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:55.333632+00:00
-- url     : https://prove2.me/theorems/3ead363e-8b65-4024-930a-873dd71e7446
-- title:
--   Lemma 4.4, p. 146 — A holds at α, fails at β ⇒ Armijo–Wolfe steps in [α, β] have nonzero measure
-- statement:
--   Let $h:\mathbb R\to\mathbb R$, let $s<0$, and let $0<c_1<c_2<1$. Write $A(t)$ for the Armijo condition $h(t)<c_1st$ and $W(t)$ for the Wolfe condition "$h$ is differentiable at $t$ with $h'(t)>c_2s$". Suppose $0<\alpha<\beta$, that $A(\alpha)$ holds, that $A(\beta)$ fails, and that $h$ is absolutely continuous on $[\alpha,\beta]$. Then
--   $$\lambda\bigl(\{t\in[\alpha,\beta] : A(t) \text{ and } W(t)\}\bigr)\neq 0,$$
--   where $\lambda$ is Lebesgue measure.
--
--   This is the local ingredient of the existence theorem 4.5 and of the convergence theorem 4.7: any bracket on whose left end the Armijo condition holds and on whose right end it fails contains a set of positive measure of Armijo–Wolfe steps.
--
--   **Formalization Note.** The lemma as printed does not restate the standing assumptions $c_1<c_2$ in $(0,1)$ (p. 146) and $s<0$ (Assumption 4.1); its proof uses $c_2s\le c_1s$. Both are added as hypotheses. "Nonzero measure" is stated in $[0,\infty]$, without conversion to a real number.
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, p. 146, Lemma 4.4

import Mathlib
import Definitions.Def_NonsmoothQN_LineSearch_Basic

open Filter Topology MeasureTheory Set

namespace NonsmoothQN.LineSearch

/-- Lemma 4.4 (p. 146). If `A` holds at `α > 0` but fails at `β > α`, and `h` is absolutely
continuous on `[α, β]`, then the Armijo–Wolfe steps in `[α, β]` have nonzero measure. The
standing constants `0 < c₁ < c₂ < 1` (p. 146) and `s < 0` (Assumption 4.1) are added. -/
theorem lemma_4_4_aw_measure_pos (h : ℝ → ℝ) (c₁ c₂ s α β : ℝ)
    (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1) (hs : s < 0)
    (hα : 0 < α) (hαβ : α < β)
    (hAα : ArmijoA h c₁ s α) (hAβ : ¬ ArmijoA h c₁ s β)
    (hac : AbsolutelyContinuousOnInterval h α β) :
    volume {t | t ∈ Set.Icc α β ∧ ArmijoA h c₁ s t ∧ WolfeW h c₂ s t} ≠ 0 := by sorry

end NonsmoothQN.LineSearch
