-- Prove2me | Theorems.Thm_NegativeDP_OptEq_theorem52d
-- name    : NegativeDP.OptEq.theorem52d
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:54:37.203974+00:00
-- url     : https://prove2.me/theorems/cd35c4eb-597c-42f0-a4be-17e91e48e82a
-- title:
--   Theorem 5.2(d) (N) — monotone limits under $U$
-- statement:
--   Let $\pi = (f_1,f_2,\dots)$ be a Markov policy of a negative dynamic programming problem, $T_n$ the operator of $f_n$ and $U = \sup_n T_n$. Let $u_1,u_2,\dots$ be a sequence in $M(S)$.
--
--   1. If $u_j \downarrow u$ (the sequence is non-increasing and $u = \inf_j u_j$), then $\inf_j Uu_j \ge Uu$.
--   2. If $u_j \uparrow u$ (the sequence is non-decreasing and $u = \sup_j u_j$), then $\sup_j Uu_j \le Uu$, with equality at every state $s$ such that
--   $$\sup_j T_n u_j(s) > -\infty \qquad\text{for all } n.$$
--
--   The second part is the continuity of $U$ along increasing sequences that makes $\lim_n U^n v$ a conserved function in Lemma 6.2.
--
--   The paper states Theorem 5.2 for the discounted, positive and negative cases; this item is the negative case. **Formalization Note** Each $u_j\in M(S)$ is a hypothesis; the limits are stated as pointwise infimum and supremum of the monotone sequence. All statements are pointwise in $s$, with values in `EReal`.
-- source:
--   Strauch, Negative Dynamic Programming, Ann. Math. Statist. 37 (1966), p. 879, Theorem 5.2(d)

import Mathlib
import Definitions.Def_DiscountedDP_Stationary_Model
import Definitions.Def_DiscountedDP_Stationary_Return
import Definitions.Def_DiscountedDP_Stationary_Operators
import Definitions.Def_NegativeDP_OptEq_Model
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal
open DiscountedDP.Stationary (Hist Plan MarkovPlan stationary IsGenerated IsGeneratedPlan)

namespace NegativeDP.OptEq

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S] [Nonempty S]
  [MeasurableSpace A] [StandardBorelSpace A] [Nonempty A]

/-- Strauch (1966), Theorem 5.2(d), p. 879, negative case. For a sequence `uⱼ` in `M(S)`:
if `uⱼ ↓ u` then `infⱼ Uuⱼ ≥ Uu`; if `uⱼ ↑ u` then `supⱼ Uuⱼ ≤ Uu`, with equality at every
state where `supⱼ Tₙuⱼ > −∞` for all `n`. -/
theorem theorem52d (P : NegativeDP.Stationary.Problem S A) (π : MarkovPlan S A) (uj : ℕ → S → EReal) (u : S → EReal)
    (huj : ∀ j, NegativeDP.Stationary.IsNegM (uj j)) :
    (Antitone uj → (∀ s, u s = ⨅ j, uj j s) →
        ∀ s, U P π u s ≤ ⨅ j, U P π (uj j) s) ∧
    (Monotone uj → (∀ s, u s = ⨆ j, uj j s) →
        (∀ s, ⨆ j, U P π (uj j) s ≤ U P π u s) ∧
        ∀ s, (∀ n, ⊥ < ⨆ j, NegativeDP.Stationary.T P (π n) (uj j) s) → ⨆ j, U P π (uj j) s = U P π u s) := by sorry

end NegativeDP.OptEq
