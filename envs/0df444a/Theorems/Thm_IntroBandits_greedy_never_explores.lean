-- Prove2me | Theorems.Thm_IntroBandits_greedy_never_explores
-- name    : IntroBandits.greedy_never_explores
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-24T02:34:14.06599+00:00
-- url     : https://prove2.me/theorems/f9a5640f-6dc4-4ec5-b580-1e53e891b87d
-- title:
--   Theorem 11.7: with probability at least $\mu^0_1 - \mu^0_2$, GREEDY never chooses arm 2
-- statement:
--   **Theorem 11.7.** With probability at least $\mu^0_1 - \mu^0_2$, GREEDY never chooses arm 2.
--
--   Formally: for every prior $P$ (a probability measure on mean vectors, supported on the finite set $F \subseteq [0,1]^2$, correlated or not), every reward family, every bandit policy $\pi$ that is GREEDY (11.2) and every horizon $T$, under the joint law of $(\mu, H_T)$ of the run,
--   $$\Pr[\,a_t = 1 \text{ for every round } t \le T\,] \ge \mu^0_1 - \mu^0_2 ,$$
--   where $\mu^0_a = \mathbb{E}[\mu_a]$ is the prior mean. The probability is written as $\mathrm{ENNReal.ofReal}(\mu^0_1 - \mu^0_2) \le \Pr[\cdot]$, so the statement is trivial when $\mu^0_1 < \mu^0_2$, as the book's is.
-- source:
--   Slivkins, Introduction to Multi-Armed Bandits, arXiv:1904.07272 (FnT ML 12, 2019), §11.2 p. 148, Theorem 11.7, with its proof by optional stopping

import Definitions.Def_IntroBandits_Agents

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace IntroBandits

theorem greedy_never_explores (P : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure P]
    (F : Finset (Fin 2 → ℝ)) (hF : P (↑F)ᶜ = 0)
    (hunit : ∀ μ ∈ F, ∀ a, μ a ∈ Set.Icc (0 : ℝ) 1) (fam : RewardFamily)
    {π : BanditPolicy 2} (hπ : IsGreedy P F fam π) (T : ℕ) :
    ENNReal.ofReal (priorMean P F 0 - priorMean P F 1) ≤
      jointMeasure P F fam π T (Set.univ ×ˢ {h | ∀ t, (h t).1 = 0}) := by sorry

end IntroBandits
