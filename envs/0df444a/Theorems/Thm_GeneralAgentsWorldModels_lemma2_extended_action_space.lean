-- Prove2me | Theorems.Thm_GeneralAgentsWorldModels_lemma2_extended_action_space
-- name    : GeneralAgentsWorldModels.lemma2_extended_action_space
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:35:43.894981+00:00
-- url     : https://prove2.me/theorems/aaf6393a-fc41-4392-8d1c-31e458623269
-- title:
--   Lemma 2: extending the action space cannot lower the optimal success probability
-- statement:
--   Let the environment $P$ satisfy Assumption 1, and extend its action set by one action $\bar a$, $A'=A\cup\{\bar a\}$, with a transition function $P'$ satisfying $P'_{ss'}(a)=P_{ss'}(a)$ for all $a\in A$ and with $P'_{s\cdot}(\bar a)$ an arbitrary probability distribution. Then for every composite goal $\psi$ (over $A$, read over $A'$) and every initial state $s_0$,
--
--   $$\max_\pi P'(\tau\models\psi\mid\pi,s_0)\ \ge\ \max_\pi P(\tau\models\psi\mid\pi,s_0).$$
--
--   In Lemma 6 this lets an upper bound be computed in an environment with an extra "teleport" action.
--
--   **Formalization Note** $A'$ is the type of optional actions, with $\bar a$ the empty option; maxima over policies are suprema over deterministic history-dependent policies.
-- source:
--   Richens, Abel, Bellot and Everitt, General agents contain world models, arXiv:2506.01622v5 (ICML 2025), Appendix A.6, Lemma 2, eq. (7), p. 14

import Mathlib
import Definitions.Def_GeneralAgentsWorldModels_Basic

open Finset

namespace GeneralAgentsWorldModels

theorem lemma2_extended_action_space {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (M : CMP S A) (hM : SatisfiesAssumption1 M) (M' : CMP S (Option A))
    (hM' : ∀ s a s', M'.P s (some a) s' = M.P s a s') (ψ : CompGoal S A) (s₀ : S) :
    optProb M ψ s₀ ≤ optProb M' (liftGoal ψ) s₀ := by sorry

end GeneralAgentsWorldModels
