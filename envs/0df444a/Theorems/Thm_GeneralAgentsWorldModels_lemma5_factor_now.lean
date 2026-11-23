-- Prove2me | Theorems.Thm_GeneralAgentsWorldModels_lemma5_factor_now
-- name    : GeneralAgentsWorldModels.lemma5_factor_now
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T17:37:32.8928+00:00
-- url     : https://prove2.me/theorems/4ceaaa7b-041a-426d-ad23-d638a47a94b4
-- title:
--   Lemma 5: factoring a Now sub-goal
-- statement:
--   Let the environment satisfy Assumption 1, let $\psi=\langle\varphi_1,\varphi_2,\dots,\varphi_L\rangle$ with $\varphi_1=\top([A=a])$, and let $\pi$ be a deterministic policy with $\pi(s_0)=a$, i.e. it takes action $a$ at time $0$ from $s_0$. Then
--
--   $$P(\tau\models\psi\mid s_0,\pi)=P\big(\tau\models\langle\varphi_2,\dots,\varphi_L\rangle\mid s_0,\pi\big).$$
--
--   **Formalization Note** As in eq. (4), the remaining sub-goals after a Now sub-goal are evaluated from the same time step; $\pi$ may depend on the whole history.
-- source:
--   Richens, Abel, Bellot and Everitt, General agents contain world models, arXiv:2506.01622v5 (ICML 2025), Appendix A.6, Lemma 5, eqs. (22)-(24), p. 15

import Mathlib
import Definitions.Def_GeneralAgentsWorldModels_Basic

open Finset

namespace GeneralAgentsWorldModels

theorem lemma5_factor_now {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (M : CMP S A) (hM : SatisfiesAssumption1 M) (π : Policy S A) (a : A)
    (rest : SeqGoal S A) (s₀ : S) (h₀ : π [] s₀ = a) :
    succProb M [nowAct a :: rest] π s₀ = succProb M [rest] π s₀ := by sorry

end GeneralAgentsWorldModels
