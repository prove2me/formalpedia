-- Prove2me | Theorems.Thm_KaelblingPOMDP_Witness_useful_subtree_suffices
-- name    : KaelblingPOMDP.Witness.useful_subtree_suffices
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:12:55.415712+00:00
-- url     : https://prove2.me/theorems/2fb30e8b-50f6-405f-b589-ab511a943acf
-- title:
--   §4.3, p. 113 — for every belief and subtree some useful subtree in V_{t−1} is at least as good
-- statement:
--   Let $\langle S, A, T, R, \Omega, O\rangle$ be a POMDP satisfying the standing hypotheses and $t \ge 2$. Let $\mathcal V_{t-1}$ be the set of useful $(t-1)$-step policy trees. For every belief state $b$ and every $(t-1)$-step tree $q$ there is $q' \in \mathcal V_{t-1}$ with
--   $$V_q(b) \le V_{q'}(b).$$
--
--   In the paper's words, there is never any reason to include a nonuseful policy subtree. This is why value iteration may restrict the subtrees of new $t$-step trees to $\mathcal V_{t-1}$.
--
--   **Formalization Note** The statement is written for $(n+1)$-step trees, $n \ge 0$; `usefulTrees M n` is the set of useful ones among all $(n+1)$-step trees.
-- source:
--   Kaelbling, Littman, Cassandra, Planning and acting in partially observable stochastic domains, Artificial Intelligence 101:99–134 (1998), DOI 10.1016/S0004-3702(98)00023-X, p. 113, §4.3

import Mathlib
import Definitions.Def_KaelblingPOMDP_Witness_Useful

namespace KaelblingPOMDP.Witness

open Finset

universe u

/-- §4.3, p. 113 (Kaelbling, Littman, Cassandra, *Planning and acting in partially observable stochastic domains*,
Artificial Intelligence 101:99–134 (1998)): "For any belief state and any choice of policy
subtree, there is always a useful subtree that is at least as good at that state": for every belief
state `b` and every (n + 1)-step tree `q` there is a tree `q'` in `V_{n+1}`, the set of useful
(n + 1)-step trees, with `V_q(b) ≤ V_{q'}(b)`. -/
theorem useful_subtree_suffices {S A Ω : Type u} [Fintype S] [DecidableEq S] [Nonempty S] [Fintype A] [DecidableEq A]
    [Nonempty A] [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (M : POMDP S A Ω) (hM : M.IsValid) (n : ℕ) :
    ∀ b ∈ stdSimplex ℝ S, ∀ q : PolicyTree A Ω n,
      ∃ q' ∈ usefulTrees M n, valueAt M q b ≤ valueAt M q' b := by sorry

end KaelblingPOMDP.Witness
