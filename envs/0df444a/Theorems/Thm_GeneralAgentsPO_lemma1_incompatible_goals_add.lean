-- Prove2me | Theorems.Thm_GeneralAgentsPO_lemma1_incompatible_goals_add
-- name    : GeneralAgentsPO.lemma1_incompatible_goals_add
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T05:17:53.941798+00:00
-- url     : https://prove2.me/theorems/68dfc110-56b6-478d-94ba-0850484b9c8f
-- title:
--   Lemma 1: probabilities of incompatible goals add
-- statement:
--   Let $(\mathcal S,\mathcal A,P)$ be a finite cMDP and let $\varphi_1,\varphi_2$ be incompatible goals: no history satisfies both. Then for every policy $\pi$ and every state $s$,
--
--   $$\Pr(\varphi_1\vee\varphi_2\mid\pi,s)=\Pr(\varphi_1\mid\pi,s)+\Pr(\varphi_2\mid\pi,s),$$
--
--   and consequently, for every $s$,
--
--   $$\max_\pi\Pr(\varphi_1\vee\varphi_2\mid\pi,s)\le\max_\pi\Pr(\varphi_1\mid\pi,s)+\max_\pi\Pr(\varphi_2\mid\pi,s).$$
--
--   This additivity is what turns success probabilities of single goals $\varphi_{b,w}$ into binomial probabilities for the disjunctions $\rho_{b,r}$, $\psi_{b,k}$ and $\chi_{b,k}$.
--
--   **Formalization Note** The disjunction $\varphi_1\vee\varphi_2$ of two goals (each a list of sequential goals) is the concatenation of the two lists, and $\max_\pi$ is a supremum over all stochastic history-dependent policies.
-- source:
--   Cifuentes, General Agents Contain World Models, even under Partial Observability and Stochasticity, arXiv:2602.03146v1 (2026), Section 2, Lemma 1, p. 5

import Mathlib
import Definitions.Def_GeneralAgentsPO_Basic

open GeneralAgentsWorldModels

namespace GeneralAgentsPO

theorem lemma1_incompatible_goals_add {S A : Type*} [Fintype S] [Fintype A]
    (M : CMP S A) (φ₁ φ₂ : CompGoal S A) (h : IsIncompatible φ₁ φ₂) :
    (∀ (π : StochPolicy S A) (s : S),
      goalProb M π (φ₁ ++ φ₂) s = goalProb M π φ₁ s + goalProb M π φ₂ s) ∧
    ∀ s : S, optValue M (φ₁ ++ φ₂) s ≤ optValue M φ₁ s + optValue M φ₂ s := by sorry

end GeneralAgentsPO
