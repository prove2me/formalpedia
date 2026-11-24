-- Prove2me | Theorems.Thm_GeneralAgentsWorldModels_lemma1_markov_policy_reaches_state
-- name    : GeneralAgentsWorldModels.lemma1_markov_policy_reaches_state
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-23T17:34:54.46593+00:00
-- url     : https://prove2.me/theorems/ca785dbc-3a5b-4b2d-b41b-8864b3c0ed3f
-- title:
--   Lemma 1: a deterministic Markov policy reaches any state with probability 1
-- statement:
--   Let the environment satisfy Assumption 1 (a finite, stationary, communicating controlled Markov process with at least two actions) and let $s'\in S$. Then there is a deterministic Markov policy $\mu:S\to A$ (taking action $\mu(s_t)$ at time $t$) that, started from any state $s\ne s'$, eventually reaches $s'$ with probability one:
--
--   $$P\big(\tau\models\Diamond[S=s']\mid\mu,s\big)=1\qquad\text{for all }s\ne s'.$$
--
--   This is the navigation primitive used to return to a fixed state between the repeated trials of Lemma 6.
-- source:
--   Richens, Abel, Bellot and Everitt, General agents contain world models, arXiv:2506.01622v5 (ICML 2025), Appendix A.6, Lemma 1, p. 13 (Assumption 1, Section 2.2, p. 2)

import Mathlib
import Definitions.Def_GeneralAgentsWorldModels_Basic

open Finset

namespace GeneralAgentsWorldModels

theorem lemma1_markov_policy_reaches_state {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A]
    (M : CMP S A) (hM : SatisfiesAssumption1 M) (s' : S) :
    ∃ μ : S → A, ∀ s : S, s ≠ s' →
      succProb M [[evState s']] (fun _ x => μ x) s = 1 := by sorry

end GeneralAgentsWorldModels
