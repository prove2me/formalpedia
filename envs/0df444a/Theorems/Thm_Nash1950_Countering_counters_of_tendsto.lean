-- Prove2me | Theorems.Thm_Nash1950_Countering_counters_of_tendsto
-- name    : Nash1950.Countering.counters_of_tendsto
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T13:30:44.381412+00:00
-- url     : https://prove2.me/theorems/dfe89e46-90b1-4c5b-8a54-3cad3e96082d
-- title:
--   Sequential closedness of the countering correspondence
-- statement:
--   Let $P_k,Q_k$ be sequences of mixed-strategy profiles in a finite game, converging respectively to $P$ and $Q$. If $Q_k$ counters $P_k$ at every index, then $Q$ counters $P$:
--
--   $$
--   P_k\to P,\quad Q_k\to Q,\quad \forall k\;Q_k\in C(P_k)\quad\Longrightarrow\quad Q\in C(P).
--   $$
--
--   This is Nash's explicit sequential formulation of the closed-graph property.
--
--   **Formalization Note.** Convergence uses the product topology on the finite product of real strategy vectors. The sequence index is $k$ to distinguish it from the number of players. Each $P_k$ is explicitly a mixed profile; each $Q_k$ is one by the definition of countering.
-- source:
--   Nash, Equilibrium points in n-person games, Proc. Natl. Acad. Sci. USA 36 (1950), p. 49, ¶3, sentences 3–4 (PDF p. 3)

import Mathlib
import Definitions.Def_agt_games
import Definitions.Def_Nash1950_Countering_Setting

open Filter

namespace Nash1950.Countering

theorem counters_of_tendsto {ι : Type*} [Fintype ι] [DecidableEq ι]
    (S : ι → Type*) [∀ i, Fintype (S i)]
    (u : ι → (∀ i, S i) → ℝ) :
    ∀ (P Q : ℕ → ∀ i, S i → ℝ) (P₀ Q₀ : ∀ i, S i → ℝ),
      (∀ k, AGT.IsMixedProfile (P k)) →
      Tendsto P atTop (nhds P₀) → Tendsto Q atTop (nhds Q₀) →
      (∀ k, Counters u (P k) (Q k)) → Counters u P₀ Q₀ := by sorry

end Nash1950.Countering
