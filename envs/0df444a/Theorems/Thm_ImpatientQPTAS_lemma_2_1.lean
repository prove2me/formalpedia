-- Prove2me | Theorems.Thm_ImpatientQPTAS_lemma_2_1
-- name    : ImpatientQPTAS.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-05T21:00:32.108529+00:00
-- url     : https://prove2.me/theorems/820dd095-94ea-4839-98bd-f0b8f2bd975b
-- title:
--   Lemma 2.1 — a class-ordered policy earns $(1-6\epsilon)\,R(S^*)$
-- statement:
--   Let $\epsilon\in(0,\tfrac14)$. There is a class-ordered extended policy $S^{CO}$ such that
--   $$
--   R(S^{CO})\ge(1-6\epsilon)\,R(S)
--   $$
--   for every adaptive service policy $S$.
--
--   So, up to a factor $1-6\epsilon$, quitters can wait for stage $1$ only and stickers for the last stages, and decisions matter only for average customers.
--
--   **Formalization Note** The witness is a function of the state. Reward is counted over the stages $1,\dots,2n$, in which the printed $S^{CO}$ operates. In the printed construction (p.29), "unmarked" must be dropped and $\cup$ read as $\cap$, as Claim A.3 and the definition on p.7 require; the lemma is unaffected.
--
--   Differences from the source:
--   - generalization: S^CO keeps marks in its state (App. A.1) → the witness is a function of (t, A) only; reason: the class-ordered constraints depend only on the state, so an optimal such policy of the finite-horizon problem is at least as good; it is in particular a policy of the printed kind
--   - encoding: R(S^CO) ≥ (1 − 6ε)·R(S*) for a fixed optimal S* → the bound for every policy S; reason: S* dominates every policy, so the two say the same
--   - encoding: the reward of an extended policy over all stages → the reward over the stages 1, …, 2n; reason: S^CO operates only in these stages (App. A.2, p.31); a truncated reward is at most the full one
-- source:
--   Segev, Near-Optimal Adaptive Policies for Serving Stochastically Departing Customers, arXiv:2209.13878v1, Lemma 2.1, p.8; construction App. A.1, pp.28–29

import Mathlib
import Definitions.Def_ImpatientQPTAS_Model
import Definitions.Def_ImpatientQPTAS_Classes

namespace ImpatientQPTAS

/-- Segev, arXiv:2209.13878v1, Lemma 2.1, p.8: a class-ordered policy earns at least `1 − 6ε` of the
reward of every adaptive service policy, for `ε ∈ (0, 1/4)`.

**Formalization Note.** The printed `S*` is a fixed optimal policy, so the guarantee against every
policy `S` is the same claim. The witness `T` is a function of the state `(t, A)`: the printed `S^CO`
also keeps marks, and since the class-ordered constraints depend only on the state, an optimal
class-ordered policy of the finite-horizon problem is at least as good. Reward is counted over the
stages `1, …, 2n` in which `S^CO` operates. -/
theorem lemma_2_1 {n : ℕ} (ε : ℝ) (h0 : 0 < ε) (h1 : ε < 1 / 4) (I : Instance n)
    (hI : I.Standing) :
    ∃ T : Policy n, IsExtPolicy T ∧ ClassOrdered ε I T ∧
      ∀ S : Policy n, IsPolicy S → (1 - 6 * ε) * I.R S ≤ I.R T := by sorry

end ImpatientQPTAS
