-- Prove2me | Theorems.Thm_MDPFinance_OptimalStopping_theorem_10_3_4
-- name    : MDPFinance.OptimalStopping.theorem_10_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:46:27.255989+00:00
-- url     : https://prove2.me/theorems/2ea9ad18-c5f4-4395-9071-61a22ad11689
-- title:
--   Theorem 10.3.4 — MTP2 monotonicity for the Bayesian stopping problem
-- statement:
--   **Theorem 10.3.4** (p. 324). If the density $q(z|\theta)$ is $MTP_2$ in $z$ and $\theta$,
--   then the functions $(x,i) \mapsto J_n(x,i)$ and $i \mapsto c_n(i)$ are increasing for all $n$.
--
--   More information about a better parameter is worth more. The content is that this survives the
--   Bayesian update: the $MTP_2$ property of the *likelihood* propagates through $\hat\Phi$ into
--   monotonicity of the *value functions* in the information state.
--
--   **Two different orders are in play and neither is the coordinatewise order on a product.** On the
--   information space, $i \le i'$ means $\hat\mu(\cdot|i) \le_{lr} \hat\mu(\cdot|i')$ in the
--   **likelihood ratio order** — strictly stronger than stochastic dominance, and the one §5.4 uses. On
--   $E = \mathbb{R} \times I$ the order is $(x,i) \le (x',i')$ iff $x \le x'$ and $i \le i'$ with that
--   $I$-order.
--
--   **$MTP_2$ is a hypothesis about the model, not about the conclusion.** It constrains the offer
--   density $q$; the conclusion is about the value functions $J_n$ and the continuation values $c_n$,
--   which are built from $q$ by integration and recursion. Assuming monotonicity of $J_n$ directly
--   would make the theorem circular.
--
--   **Moderation note.** The draft's model had no Bayes structure, so the monotonicity claim was refutable; now the model carries the Bayes update (see the definitions), and `c_n` is compared for `n ≥ 1` (the book's `c_0` is undefined), in `[-∞,∞]`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 324 (PDF 332), Theorem 10.3.4

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Applications

open MeasureTheory

namespace MDPFinance.OptimalStopping

/-- **Theorem 10.3.4** (p. 324). If the density `q(z|θ)` is `MTP_2` in `z` and `θ`, then
`(x,i) ↦ J_n(x,i)` and `i ↦ c_n(i)` are increasing for all `n` (`n ≥ 1` for `c_n`), for the
likelihood-ratio order on the information states. -/
theorem theorem_10_3_4 {I : Type*} [MeasurableSpace I] (M : GenBayesStopping I)
    (hMTP2 : IsMTP2 M.q) :
    (∀ (n : ℕ) (p p' : ℝ × I), M.Ele p p' → M.J n p.1 p.2 ≤ M.J n p'.1 p'.2) ∧
    (∀ (n : ℕ) (i i' : I), 1 ≤ n → M.Ile i i' → M.cfun n i ≤ M.cfun n i') := by sorry

end MDPFinance.OptimalStopping
