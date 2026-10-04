-- Prove2me | Theorems.Thm_MDPFinance_OptimalStopping_theorem_10_3_3
-- name    : MDPFinance.OptimalStopping.theorem_10_3_3
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:46:27.559202+00:00
-- url     : https://prove2.me/theorems/85db12ae-7117-4dae-8527-a405048f1471
-- title:
--   Theorem 10.3.3 — the secretary problem's optimal rule and its 1/e limit
-- statement:
--   **Theorem 10.3.3** (p. 323). The optimal stopping time for the secretary problem is as
--   follows: make interviews with the first $k^*$ candidates and reject them all (where $k^*$ is given
--   by equation **(10.5)**). Afterwards, take the first candidate who is better than her predecessors.
--   The probability for choosing the best candidate is then given by $\frac{k^*}{N}h(k^*)$. … It holds
--   that
--   $$ \lim_{N\to\infty}\frac{k^*(N)}{N} = \frac1e . $$
--
--   The classical answer, and the reason the problem is famous: "if the number of candidates is large,
--   approximately the first 37% will be rejected and the next one is accepted who is better than her
--   predecessors."
--
--   The three claims are separately substantial. **The rule** is that the states in which stopping is
--   optimal are exactly those above $k^*$, which is what "reject the first $k^*$, then take the first
--   leader" means for this chain: the state $x$ records the time at which a candidate is leading, so
--   entering $\{x > k^*\}$ *is* meeting a candidate better than all her predecessors after the
--   rejection phase. **The probability** is the value at the initial state, $V_0(1)$, which the book
--   identifies as "the maximal probability for choosing the best candidate" (p. 322). **The $1/e$
--   limit** is a statement about the family $k^*(N)$ as $N$ varies, so it is phrased against the
--   horizon-indexed $k^*(N)$ rather than one fixed problem.
--
--   **Moderation note.** Checked; unchanged (the stopping-set identity holds on the states `{1,…,N}` for every `n ≤ k^*`, since the closed form of Proposition 10.3.2 is independent of `n` there).
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 323 (PDF 331), Theorem 10.3.3

import Mathlib
import Definitions.Def_MDPFinance_OptimalStopping_Applications

open Filter Topology

namespace MDPFinance.OptimalStopping

/-- **Theorem 10.3.3** (p. 323). The optimal rule: reject the first `k^*` candidates, then take
the first leader — the stopping sets `{V_n = g}` are `{x > k^*}` on the states; the probability of
choosing the best candidate is `V_0(1) = (k^*/N) h(k^*)`; and `k^*(N)/N → 1/e`. -/
theorem theorem_10_3_3 (S : Secretary) :
    (∀ n : ℕ, n ≤ S.kStar →
      {x : ℕ | x ∈ Finset.Icc 1 S.N ∧ S.V n x = S.g x} =
        {x : ℕ | x ∈ Finset.Icc 1 S.N ∧ S.kStar < x}) ∧
    S.V 0 1 = ((S.kStar : ℝ) / (S.N : ℝ)) * S.h S.kStar ∧
    Tendsto (fun N : ℕ => (secretaryKStar N : ℝ) / (N : ℝ)) atTop (𝓝 (1 / Real.exp 1)) := by sorry

end MDPFinance.OptimalStopping
