-- Prove2me | Theorems.Thm_NetFeePlatform_Competition_foc_best_response
-- name    : NetFeePlatform.Competition.foc_best_response
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T08:30:55.355497+00:00
-- url     : https://prove2.me/theorems/0c40e55f-5ff4-466f-87e6-414ed04d06ce
-- title:
--   (36), proof of Lemma 2, p. 43 — under Logit demand with γ ≤ 27/8, the pricing formula (14) gives a global best response
-- statement:
--   Consider the one-sided Logit platform game with $J$ platforms, outside-option weight $w\ge0$, common marginal cost $c$, common interaction value $\gamma$ and no interoperability, so that platform $j$'s profit is $\pi^j(t)=(t^j+\gamma n^j(t)-c)\,n^j(t)$ with $n^j(t)=e^{-t^j}/(w+\sum_k e^{-t^k})$. Assume that $w>0$ or $J\ge2$, and that
--   $$\gamma\le\frac{27}{8}.$$
--
--   Fix the other platforms' net fees. If platform $j$'s net fee satisfies the Logit pricing formula
--   $$t^j=c+\frac{1}{1-n^j(t)}-2\gamma\,n^j(t),$$
--   then $t^j$ is a global best response: for every $s\in\mathbb R$, the profit of platform $j$ when it deviates to the net fee $s$ is at most its profit at $t^j$.
--
--   This is the Logit form of the concavity condition (36): profit, viewed as a function of the platform's own share, is concave when $2\gamma\le 1/(n^j(1-n^j)^2)$, whose right-hand side has minimum $27/4=6.75$ at $n^j=1/3$. It is the step that turns solutions of the pricing formulas into equilibria.
--
--   **Formalization Note** The bound $27/8=3.375$ is the paper's $2\gamma\le6.75$. The conclusion quantifies over every deviation $s\in\mathbb R$, not over a neighbourhood. The paper states Lemma 2 for general demand under Assumption A1; this item is its Logit form.
-- source:
--   Ekmekci, White & Wu, Platform Competition and Interoperability: The Net Fee Model, accepted working-paper version (December 12, 2024), p. 41, Lemma 2; p. 43, (36), Appendix E.1.1, proof of Lemma 2

import Mathlib
import Definitions.Def_NetFeePlatform_Competition_Setting

namespace NetFeePlatform.Competition
theorem foc_best_response {J : ℕ} (w c γ : ℝ) (hw : 0 ≤ w) (hJ : 0 < w ∨ 2 ≤ J)
    (hγ : γ ≤ 27 / 8) (t : Fin J → ℝ) (j : Fin J)
    (hfoc : t j = c + 1 / (1 - demand w t j) - 2 * γ * demand w t j) :
    ∀ s : ℝ, profit w c γ 0 (Function.update t j s) j ≤ profit w c γ 0 t j := by sorry
end NetFeePlatform.Competition
