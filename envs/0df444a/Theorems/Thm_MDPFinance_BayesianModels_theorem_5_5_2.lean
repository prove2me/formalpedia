-- Prove2me | Theorems.Thm_MDPFinance_BayesianModels_theorem_5_5_2
-- name    : MDPFinance.BayesianModels.theorem_5_5_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T22:20:33.904201+00:00
-- url     : https://prove2.me/theorems/d54edb65-410b-4133-a36f-3648f19dde82
-- title:
--   Theorem 5.5.2 — the one-known-arm bandit's monotonicity and stopping properties
-- statement:
--   **Theorem 5.5.2.** In the one-known-arm bandit (arm 1's success probability $p_1$ known,
--   information state $(m,n)$ for arm 2 alone), let $\pi^* = (f_N^*,\dots,f_1^*)$ be the optimal
--   policy (same largest-maximizer construction as Theorem 5.5.1, via $d_k(m,n)$). Then:
--
--   a) $f_k^*(m,n)$ is increasing in $(m,n)$ w.r.t. the order $(m,n) \le (m',n') :\Leftrightarrow m
--   \le m',\, n \ge n'$ (more/earlier successes and fewer/later failures at arm 2 make arm 2 more
--   attractive).
--
--   b) Stay-on-a-winner for arm 2: $f_{k+1}^*(m,n)=2 \Rightarrow f_k^*(m+1,n)=2$.
--
--   c) Stopping rule for arm 1: $f_{k+1}^*(m,n)=1 \Rightarrow f_k^*(m,n)=1$ — once the known arm is
--   chosen, it is chosen forever (no more information about arm 2 is ever gained).
--
--   d) Partly myopic: $p(m,n) \ge p_1 \Rightarrow f_k^*(m,n)=2$ for every $k \in \mathbb N$ (the
--   *converse* is false, and is not asserted here).
--
--   These four properties turn the qualitative "explore-then-exploit" intuition for a bandit against
--   a known benchmark into precise, checkable structural facts about the optimal policy, each
--   following from Theorem 5.4.10's general monotonicity machinery specialized to this concrete
--   two-dimensional information state.
--
--   **Formalization Note.** The four properties are stated as four independent conjuncts, matching
--   the book's own a)-d) structure, so each can be checked against the page individually; part d)'s
--   false converse is deliberately not stated as an iff.
--
--   **Moderation note.** Parts a)-c) are stated for $k\ge 1$: the draft's part c) at $k=0$ compared $f^*_1$ with `f 0`, which is not a decision rule of the policy, and was refutable whenever $p(m,n)<p_1$. Optimality now also states $V^\pi_N\le J_N$ for every Markov policy.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 170, Theorem 5.5.2

import Mathlib
import Definitions.Def_MDPFinance_BayesianModels_OneKnownArmBandit

open MeasureTheory

namespace MDPFinance.BayesianModels

/-- Theorem 5.5.2 (Bäuerle–Rieder, p. 170, PDF 183). Suppose the success probability at arm 1 is
known (`p_1 ∈ (0,1)`). Let `π^* = (f_N^*,\dots,f_1^*)` be the optimal policy (`f_k^*(m,n) = 2` if
`d_k(m,n) ≥ 0`, `1` otherwise, the largest maximizer of the one-step problem with `k-1` stages
remaining — the same construction as Theorem 5.5.1, specialized here — arms coded `0`/`1` for
`1`/`2`). Then it holds: a) `f_k^*(m,n)` is increasing in `(m,n)` w.r.t. the order `(m,n) ≤
(m',n') :⇔ m ≤ m', n ≥ n'` (Eq. (5.12), p. 169, PDF 182). b) The stay-on-a-winner property for
arm 2 holds, i.e. `f_{k+1}^*(m,n) = 2 ⇒ f_k^*(m+1,n) = 2`. c) The stopping rule for arm 1 holds,
i.e. `f_{k+1}^*(m,n) = 1 ⇒ f_k^*(m,n) = 1`. d) The optimal policy is partly myopic:
`p(m,n) ≥ p_1 ⇒ f_k^*(m,n) = 2`, for all `k ∈ ℕ`. (The converse of d) is false — not asserted
here, per the book's own remark.) All clauses about `f_k^*` are for `k ∈ ℕ`, i.e. `k ≥ 1` (`f_0^*`
is not a decision rule of the policy); optimality is stated as `V^{π^*}_N = J_N` together with
`V^π_N ≤ J_N` for every Markov policy `π`. -/
theorem theorem_5_5_2 (p1 β : ℝ) (hp1_0 : 0 < p1) (hp1_1 : p1 < 1) (hβ0 : 0 < β) (hβ1 : β ≤ 1)
    (N : ℕ) (f : ℕ → KnownArmState → Fin 2)
    (hf : ∀ k mn, f k mn = if 0 ≤ dK p1 β k mn then (1 : Fin 2) else 0) :
    (∀ mn, VpiK p1 β f N mn = JK p1 β N mn) ∧
      (∀ (g : ℕ → KnownArmState → Fin 2) (mn : KnownArmState), VpiK p1 β g N mn ≤ JK p1 β N mn) ∧
      (∀ k, 1 ≤ k → ∀ m n m' n', m ≤ m' → n' ≤ n → f k (m, n) ≤ f k (m', n')) ∧
      (∀ k, 1 ≤ k → ∀ m n, f (k + 1) (m, n) = 1 → f k (m + 1, n) = 1) ∧
      (∀ k, 1 ≤ k → ∀ m n, f (k + 1) (m, n) = 0 → f k (m, n) = 0) ∧
      (∀ k ≥ 1, ∀ mn, p1 ≤ pK mn → f k mn = 1) := by sorry

end MDPFinance.BayesianModels
