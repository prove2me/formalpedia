-- Prove2me | Theorems.Thm_Gronemeier_oneWay_disjointness_lower_bound
-- name    : Gronemeier.oneWay_disjointness_lower_bound
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-20T19:30:21.053578+00:00
-- url     : https://prove2.me/theorems/9dcd1eca-034c-4e24-af3b-237fb527af71
-- title:
--   Gronemeier's multi-party disjointness lower bound — one-way protocols with error 1/3 need Ω(N/q²) bits per message
-- statement:
--   **Statement.** There is an absolute constant $c > 0$ with the following property. Let $q \ge 2$ players hold sets $S_0, \dots, S_{q-1} \subseteq [N]$, and consider a randomized one-way sequential protocol with $K$ memory states:
--   - an initial state is drawn from a distribution $\mu_0$ on $[K]$;
--   - for $i = 0, 1, \dots, q-1$ in turn, player $i$ replaces the current state $s$ by a state drawn from a distribution $\mathrm{step}_i(s, S_i)$, which depends only on $i$, $s$ and the player's own set $S_i$ (fresh private randomness);
--   - the answer is $\mathrm{out}(s) \in \{\mathrm{true}, \mathrm{false}\}$ of the final state $s$.
--
--   Suppose the protocol solves promise set disjointness with error at most $1/3$:
--   - if the sets are pairwise disjoint, it answers $\mathrm{true}$ with probability at most $1/3$;
--   - if some $x$ lies in every $S_i$ and the sets $S_i \setminus \{x\}$ are pairwise disjoint, it answers $\mathrm{false}$ with probability at most $1/3$.
--
--   Then $c \cdot N \le q^2 \log_2 K$.
--
--   **Relation to the source.** Gronemeier (STACS 2009) proves that every randomized number-in-hand blackboard protocol for $q$-party promise set disjointness on $[N]$ with a sufficiently small constant error communicates $\Omega(N/q)$ bits in total. A one-way sequential protocol is a blackboard protocol in which each player writes one message, its state, of $\lceil \log_2 K \rceil$ bits, so $q \lceil \log_2 K \rceil = \Omega(N/q)$. Error $1/3$ is reduced to any smaller constant by running a constant number of independent copies in parallel and taking the majority answer, which multiplies $\log_2 K$ by a constant. This is the form in which Doron-Arad and Naor apply the bound in the proof of Lemma 6.1 of *A Tight $\widetilde\Omega(\sqrt m)$ Information-theoretic Lower Bound for Randomized Online Set Cover* (STOC 2027 submission #1160): there the $q$ players simulate a streaming algorithm with $S$ bits of memory on their forcing batches, one after another.
--
--   **Lean encoding.** The states are `Fin K`, the distributions are `PMF`s, the protocol's final law is the `List.foldl` of `PMF.bind` over the players `0, …, q-1`, and the error probabilities are sums in `ℝ≥0∞`. For $K = 0$ there is no initial distribution, so that case is vacuous; for $K = 1$ the conclusion forces $N = 0$, consistent with a constant answer being unable to separate the two cases when $N \ge 1$.
--
--   Reference: A. Gronemeier, *Asymptotically optimal lower bounds on the NIH-multi-party information complexity of the AND-function and disjointness*, 26th International Symposium on Theoretical Aspects of Computer Science (STACS 2009), LIPIcs 3, pp. 505–516, https://doi.org/10.4230/LIPIcs.STACS.2009.1846.
-- source:
--   A. Gronemeier, Asymptotically optimal lower bounds on the NIH-multi-party information complexity of the AND-function and disjointness, STACS 2009, LIPIcs 3, https://doi.org/10.4230/LIPIcs.STACS.2009.1846, pp. 505–516, the Ω(N/q) randomized communication lower bound for q-party promise set disjointness, specialised to one-way sequential protocols with error 1/3, as applied in the proof of Lemma 6.1 of I. Doron-Arad and J. Naor, A Tight Ω̃(√m) Information-theoretic Lower Bound for Randomized Online Set Cover (STOC 2027 submission #1160), printed pp. 16–17

import Mathlib

namespace Gronemeier

theorem oneWay_disjointness_lower_bound :
    ∃ c : ℝ, 0 < c ∧ ∀ q N K : ℕ, 2 ≤ q →
      ∀ (init : PMF (Fin K)) (step : Fin q → Fin K → Finset (Fin N) → PMF (Fin K))
        (out : Fin K → Bool),
      (∀ S : Fin q → Finset (Fin N), (∀ i j, i ≠ j → Disjoint (S i) (S j)) →
        (∑ s, if out s = true then
          ((List.finRange q).foldl (fun μ i => μ.bind fun s => step i s (S i)) init) s
          else 0) ≤ 1 / 3) →
      (∀ S : Fin q → Finset (Fin N), ∀ x : Fin N, (∀ i, x ∈ S i) →
        (∀ i j, i ≠ j → Disjoint ((S i).erase x) ((S j).erase x)) →
        (∑ s, if out s = false then
          ((List.finRange q).foldl (fun μ i => μ.bind fun s => step i s (S i)) init) s
          else 0) ≤ 1 / 3) →
      c * (N : ℝ) ≤ (q : ℝ) ^ 2 * Real.logb 2 (K : ℝ) := by
  sorry

end Gronemeier
