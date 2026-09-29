-- Prove2me | Theorems.Thm_FoundationsML_ReinforcementLearning_bellman_optimality_condition
-- name    : FoundationsML.ReinforcementLearning.bellman_optimality_condition
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-20T04:37:21.739926+00:00
-- url     : https://prove2.me/theorems/5852936e-64f7-4cb7-9c2b-48fd5857d834
-- title:
--   Theorem 17.7 — Bellman's optimality condition
-- statement:
--   **Statement (Theorem 17.7, p. 384, PDF p. 401).** A policy $\pi$ is optimal iff for any pair
--   $(s,a)\in S\times A$ with $\pi(s)(a)>0$ the following holds:
--   $$a \in \operatorname*{argmax}_{a'\in A} Q_\pi(s,a').$$
--
--   This links the value-maximization definition of optimality (Definition 17.4) to a purely
--   local, per-state condition on the state-action value function $Q_\pi$: an optimal policy can
--   only place probability on actions that are simultaneously $Q_\pi$-maximizing.
--
--   **Formalization Note.** "$a\in\operatorname{argmax}_{a'}Q_\pi(s,a')$" is formalized as `a`
--   being a maximizer of `QFunction π P Er γ s` over `A`: `∀ a', QFunction π P Er γ s a' ≤
--   QFunction π P Er γ s a`.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 384, Theorem 17.7 (PDF p. 401)

import Mathlib
import Definitions.Def_FoundationsML_ReinforcementLearning_IsPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_IsTransitionKernel
import Definitions.Def_FoundationsML_ReinforcementLearning_IsOptimalPolicy
import Definitions.Def_FoundationsML_ReinforcementLearning_QFunction

namespace FoundationsML.ReinforcementLearning

/-- Theorem 17.7 (Bellman's optimality condition; Mohri, Rostamizadeh & Talwalkar, *Foundations
of Machine Learning*, 2nd ed., MIT Press 2018, p. 384, PDF p. 401). A policy `π` is optimal iff
for any pair `(s,a) ∈ S × A` with `π(s)(a) > 0`, `a ∈ argmax_{a'∈A} Q_π(s,a')`.

**Formalization Note.** `a ∈ argmax_{a'} Q_π(s,a')` is formalized as `a` being a maximizer of
`QFunction π P Er γ s` over `A`: `∀ a', QFunction π P Er γ s a' ≤ QFunction π P Er γ s a`. -/
theorem bellman_optimality_condition {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (π : S → A → ℝ) (hπ : IsPolicy π)
    (P : S → A → S → ℝ) (hP : IsTransitionKernel P)
    (Er : S → A → ℝ) (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) :
    IsOptimalPolicy π P Er γ ↔
      ∀ s : S, ∀ a : A, π s a > 0 →
        ∀ a' : A, QFunction π P Er γ s a' ≤ QFunction π P Er γ s a := by sorry

end FoundationsML.ReinforcementLearning
