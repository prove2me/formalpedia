-- Prove2me | Theorems.Thm_MDPFinance_StoppingFinance_theorem_11_2_2
-- name    : MDPFinance.StoppingFinance.theorem_11_2_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:49:37.276551+00:00
-- url     : https://prove2.me/theorems/c85e59ab-044a-4c5c-8467-010ded72b630
-- title:
--   Theorem 11.2.2 — the Bayesian credit granting model: monotonicity and threshold structure
-- statement:
--   For the Bayesian credit granting model it holds:
--
--   a) $J_k(s,n)$ is increasing in $(s,n)$ and increasing in $k$.
--   b) There exist thresholds $t_N^* \le \dots \le t_1^*$ such that the set of states in which the
--      credit is cancelled is given by $S_k^* := \{(s, N-k) \in E \mid s < t_k^*\}$. The optimal
--      credit policy $(f_N^*,\dots,f_1^*)$ is defined by $f_k^* := 1_{S_k^*}$.
--
--   The borrower is not rated: the bank knows only a prior $\mu_0$ on the repayment probability and
--   one signal per period. The state $(s,n)$ counts positive signals out of total signals, and the
--   theorem says the same threshold structure survives — cancel when the count of positive signals
--   falls below a boundary that rises as the horizon shortens.
--
--   **"Increasing in $(s,n)$" is for the order of p. 342**, not the coordinatewise one:
--   $(s,n) \le (s',n') \iff s \le s'$ and $n - s \ge n' - s'$, i.e. more positive signals *and* fewer
--   negative ones. Coordinatewise monotonicity in $n$ would be false — an extra signal that is
--   negative makes the state worse.
--
--   What a) rests on, from the proof: $(s,n) \mapsto c(s,n) = K_1 q(s,n) + K_0(1 - q(s,n))$ is
--   increasing — which, since $K_1 - K_0 \ge 0$, reduces to $(s,n)\mapsto q(s,n)$ being increasing, a
--   likelihood-ratio computation on the posterior — and the one-step Bayesian transition is
--   stochastically monotone for the same order. Both are carried as hypotheses about the prior and
--   the kernel, not as free facts: they are what make the monotonicity conclusion provable at all
--   rather than asserted. Neither restates the conclusion — they constrain $q$ and the one-step
--   transition, while the conclusion is about the value functions $J_k$.
--
--   The indexing runs backwards as in Theorem 11.2.1: $t_N^*$ is the threshold with $N$ periods
--   left.
--
--   **Moderation note.** The draft assumed as hypotheses that `q(s,n)` is increasing and that the transition is stochastically monotone — exactly what the book proves for every prior in the proof of a) — and used `{J_k = 0}` as the cancellation set (same boundary defect as in Theorem 11.2.1). Now the theorem has no such hypotheses, the claims are on the state space `{(s,n) | s ≤ n}`, the cancellation sets are `{c̄_k(s, N−k) < 0} = {s < t_k^*}` with `t_k^* ∈ ℕ` (`min ∅ = N−k+1`), and `f_k^*` is a maximizer of `J_{k−1}` on those states.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 342 (PDF 350), Theorem 11.2.2

import Mathlib
import Definitions.Def_MDPFinance_StoppingFinance_CreditModel

open MeasureTheory

namespace MDPFinance.StoppingFinance

/-- **Theorem 11.2.2** (p. 342). For the Bayesian credit granting model (any prior): a) `J_k(s,n)`
is increasing in `(s,n)` for the order of p. 342 and increasing in `k`; b) there are thresholds
`t_N^* ≤ … ≤ t_1^*` such that the cancellation set at stage `N − k` (with `k` periods left) is
`S_k^* = {(s, N−k) ∈ E | s < t_k^*}`, the states where extending (`c̄_k(s, N−k)`) is worse than
cancelling, and `f_k^* := 1_{S_k^*}` is optimal (`T_{f_k^*} J_{k−1} = J_k` on those states). -/
theorem theorem_11_2_2 (M : BayesCreditModel) (N : ℕ) :
    (∀ (k : ℕ) (s n s' n' : ℕ), s ≤ n → s' ≤ n' →
      BayesCreditModel.stateLe (s, n) (s', n') → M.J k s n ≤ M.J k s' n') ∧
    (∀ (j k : ℕ), j ≤ k → ∀ s n : ℕ, s ≤ n → M.J j s n ≤ M.J k s n) ∧
    (∃ tstar : ℕ → ℕ,
      (∀ (j k : ℕ), 1 ≤ j → j ≤ k → k ≤ N → tstar k ≤ tstar j) ∧
      (∀ (k s : ℕ), 1 ≤ k → k ≤ N → s ≤ N - k → (M.cbar k s (N - k) < 0 ↔ s < tstar k)) ∧
      ∀ (k s : ℕ), 1 ≤ k → k ≤ N → s ≤ N - k →
        (if s < tstar k then 0 else M.cbar k s (N - k)) = M.J k s (N - k)) := by sorry

end MDPFinance.StoppingFinance
