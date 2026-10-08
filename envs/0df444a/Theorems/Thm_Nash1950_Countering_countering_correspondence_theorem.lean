-- Prove2me | Theorems.Thm_Nash1950_Countering_countering_correspondence_theorem
-- name    : Nash1950.Countering.countering_correspondence_theorem
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:32:28.262013+00:00
-- url     : https://prove2.me/theorems/f3cba32b-af2a-473e-a389-26993437aa1b
-- title:
--   The countering correspondence has nonempty convex values and a closed graph, with equilibria as fixed points
-- statement:
--   In a finite game with a nonempty pure-strategy set for each player, let $\Sigma$ be the product space of mixed strategies and $C(P)$ the set of profiles countering $P$. Then
--
--   $$
--   \forall P\in\Sigma,\quad \varnothing\ne C(P)\subseteq\Sigma\ \text{and}\ C(P)\text{ is convex};
--   $$
--
--   whenever mixed profiles $P_k,Q_k$ converge to $P,Q$ and $Q_k\in C(P_k)$ for every $k$, one has $Q\in C(P)$; and $P\in C(P)$ if and only if $P$ is a mixed Nash equilibrium.
--
--   These are the properties of Nash's countering correspondence that underlie the equilibrium existence argument.
--
--   **Formalization Note.** Each pure-strategy set is required to be nonempty, as implicit in taking probability distributions. Convergence is in the product topology, and the sequence index is $k$. The existence of a fixed point is already the proved platform theorem `AGT.nash_existence` and is not asserted again here.
-- source:
--   Nash, Equilibrium points in n-person games, Proc. Natl. Acad. Sci. USA 36 (1950), p. 49, ¶2–¶4 (PDF p. 3)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_Nash1950_Countering_Setting

open Filter

namespace Nash1950.Countering

theorem countering_correspondence_theorem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Type*) [∀ i, Fintype (S i)] [∀ i, Nonempty (S i)]
    (u : ι → (∀ i, S i) → ℝ) :
    (∀ P : ∀ i, S i → ℝ, AGT.IsMixedProfile P →
      (counteringSet u P).Nonempty ∧
        counteringSet u P ⊆ {Q | AGT.IsMixedProfile Q} ∧
          Convex ℝ (counteringSet u P)) ∧
    (∀ (P Q : ℕ → ∀ i, S i → ℝ) (P₀ Q₀ : ∀ i, S i → ℝ),
      (∀ k, AGT.IsMixedProfile (P k)) →
      Tendsto P atTop (nhds P₀) → Tendsto Q atTop (nhds Q₀) →
      (∀ k, Counters u (P k) (Q k)) → Counters u P₀ Q₀) ∧
    (∀ P : ∀ i, S i → ℝ, Counters u P P ↔ AGT.IsMixedNash u P) := by sorry

end Nash1950.Countering
