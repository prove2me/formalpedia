-- Prove2me | Theorems.Thm_ImpatientQPTAS_theorem_1_1
-- name    : ImpatientQPTAS.theorem_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:00:24.835082+00:00
-- url     : https://prove2.me/theorems/e0633aeb-befa-404e-b4d0-9da8e7b96e81
-- title:
--   Theorem 1.1 — a deterministic quasi-polynomial-time $(1-\epsilon)$-optimal adaptive service policy
-- statement:
--   There are universal constants $c,d$ such that for every accuracy level $\epsilon\in(0,\tfrac14)$ and every instance with $n$ customers:
--
--   1. the preparation `prep` uses at most $c\,(n+1)^{c(1/\epsilon)^d\log^2(n+1)}$ operations;
--   2. the action rule `act` uses at most that many operations on every state;
--   3. the computed policy $\tilde S$ is an adaptive service policy;
--   4. for every adaptive service policy $S$,
--   $$
--   R(\tilde S)\ge(1-\epsilon)\,R(S).
--   $$
--
--   This is the main theorem of the paper: a quasi-polynomial-time approximation scheme for adaptively serving impatient customers. The guarantee is on the true rewards and departure probabilities.
--
--   **Formalization Note** The statement is about the explicit program, since in a cost monad an existential over programs would be trivial. `Work` is a counter with no randomness, so the algorithm is deterministic.
--
--   Differences from the source:
--   - reading: "O(n^{O_ε(log² n)})-time" → counted unit-cost real operations and array accesses in Work; reason: the input is real and §2.6 counts operations with no bit lengths
--   - reading: "computing an adaptive service policy" → a plan prep ε I and an action rule act, each within the bound on every input; reason: a policy is a function on ℕ × 2^[n], with 2ⁿ entries, so it must be computed implicitly; a run of at most n stages stays within the bound
--   - encoding: O(n^{O_ε(log² n)}) with O_ε(f) = poly(1/ε)·f → c·(n+1)^(c·(1/ε)^d·log²(n+1)), with c, d before ε and the instance; reason: for n ≥ 2 this is the same class; the base n + 1 keeps it meaningful at n = 1
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, Theorem 1.1, p.4; O_ε, p.4

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model
import Definitions.Def_ImpatientQPTAS_Program

namespace ImpatientQPTAS

/-- Segev, arXiv:2209.13878v1, Theorem 1.1, p.4: for any accuracy level `ε ∈ (0, 1/4)`, there is a
deterministic `O(n^{O_ε(log² n)})`-time algorithm for computing an adaptive service policy whose expected
total reward is within factor `1 − ε` of optimal.

**Formalization Note.** The statement is about the explicit program, since in a cost monad an existential
over programs is trivial. Time is counted unit-cost real operations and array accesses in `Work`, which
has no randomness, so the algorithm is deterministic. A policy has `2ⁿ` entries, so "computing" means
a plan `prep ε I` and an action rule `act`, each within the bound on every input. `c`, `d` are universal.
The guarantee is on the true `r` and `p`, against every adaptive service policy. -/
theorem theorem_1_1 :
    ∃ c d : ℕ, 0 < c ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 4 → ∀ {n : ℕ} (I : Instance n), I.Standing →
      (cost (prep ε I) : ℝ) ≤ timeBound c d ε n ∧
      (∀ (t : ℕ) (A : Finset (Fin n)), (cost (act (plan ε I) t A) : ℝ) ≤ timeBound c d ε n) ∧
      IsPolicy (policy ε I) ∧
      ∀ S : Policy n, IsPolicy S → (1 - ε) * I.R S ≤ I.R (policy ε I) := by sorry

end ImpatientQPTAS
