-- Prove2me | Theorems.Thm_OnlineSetCover_LowerBound_proposition_4_1
-- name    : OnlineSetCover.LowerBound.proposition_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T18:05:25.104056+00:00
-- url     : https://prove2.me/theorems/dd889ef7-2289-41c5-a8e7-a62adf5852bd
-- title:
--   Proposition 4.1 — on the bit family the best deterministic competitive ratio is $|\mathcal F| = k = \log_2 n$
-- statement:
--   Let $k \ge 1$, $n = 2^k$, $X = \{0, \dots, n-1\}$, and let $\mathcal F = \{F_1, \dots, F_k\}$ where $F_i$ is the set of elements of $X$ whose $i$th bit is on. Then the competitive ratio of the best deterministic online algorithm for the online set cover problem $(X, \mathcal F)$ is $|\mathcal F| = k = \log_2 n$. Precisely:
--
--   1. $|\mathcal F| = k$;
--   2. for every valid deterministic online algorithm $A$ there is a nonempty arrival sequence $\sigma$ such that some single set of $\mathcal F$ contains every element of $\sigma$ (so $\mathrm{OPT}(\sigma) = 1$) and
--   $$|\mathcal C_A(\sigma)| \;\ge\; k;$$
--   3. there is a valid deterministic online algorithm $A$ such that for every arrival sequence $\sigma$ and every offline cover $C \subseteq \mathcal F$ of $\sigma$, $|\mathcal C_A(\sigma)| \le k\,|C|$.
--
--   Parts 2 and 3 together say the optimal deterministic competitive ratio on this instance is exactly $k$. The adversary of part 2 is also the one-block step of the lower bound for the block family of Section 4.
--
--   **Formalization Note** The parameter is $k$ and $n := 2^k$, so $\log_2 n = k$ needs no logarithm. The hypothesis $k \ge 1$ is the paper's implicit one (it indexes $1 \le i \le k$); for $k = 0$ the family is empty and part 2 fails. Element $0$ lies in no $F_i$; validity asks nothing for it, and part 2's sequence avoids it because one set covers it. Algorithms may add several sets per arrival. Part 2 states $\mathrm{OPT}(\sigma) = 1$ and cost $\ge k = k \cdot \mathrm{OPT}(\sigma)$, which is how the paper's proof establishes the ratio.
-- source:
--   Alon, Awerbuch, Azar, Buchbinder, Naor, The Online Set Cover Problem, SIAM J. Comput. 39(2) (2009), p. 368, Proposition 4.1

import Mathlib
import Definitions.Def_OnlineSetCover_LowerBound_Game
import Definitions.Def_OnlineSetCover_LowerBound_BitFamily

namespace OnlineSetCover.LowerBound

/-- Proposition 4.1 (Alon et al. 2009, p. 368). On `X = {0, …, 2^k − 1}` with the family
`F = {F_1, …, F_k}` of bit sets, (1) `|F| = k`; (2) against every valid deterministic online
algorithm the adversary has a nonempty arrival sequence that one set of `F` covers (so
`OPT = 1`) while the algorithm chooses at least `k = k · OPT` sets; (3) some valid deterministic
online algorithm chooses at most `k · |C|` sets on every arrival sequence and every offline
cover `C` of it, i.e. has competitive ratio at most `k`. -/
theorem proposition_4_1 (k : ℕ) (hk : 0 < k) :
    (bitFamily k).card = k ∧
    (∀ A : OnlineAlg (Fin (2 ^ k)), IsValid (bitFamily k) A →
      ∃ σ : List (Fin (2 ^ k)), σ ≠ [] ∧
        (∃ S ∈ bitFamily k, ∀ x ∈ σ, x ∈ S) ∧ k ≤ cost A σ) ∧
    (∃ A : OnlineAlg (Fin (2 ^ k)), IsValid (bitFamily k) A ∧
      ∀ (σ : List (Fin (2 ^ k))) (C : Finset (Finset (Fin (2 ^ k)))),
        IsCoverOf (bitFamily k) C σ → cost A σ ≤ k * C.card) := by sorry

end OnlineSetCover.LowerBound
