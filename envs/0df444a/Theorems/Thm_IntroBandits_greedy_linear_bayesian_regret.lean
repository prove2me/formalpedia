-- Prove2me | Theorems.Thm_IntroBandits_greedy_linear_bayesian_regret
-- name    : IntroBandits.greedy_linear_bayesian_regret
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T02:34:39.501833+00:00
-- url     : https://prove2.me/theorems/f7e8329c-b290-4f6f-b50e-894fa8c30162
-- title:
--   Corollary 11.8: under independent priors, GREEDY suffers Bayesian regret $\ge T \cdot \frac{\alpha}{2}(\mu^0_1 - \mu^0_2)\Pr[\mu_2 > 1 - \alpha]$
-- statement:
--   **Corollary 11.8.** Consider independent priors such that $\Pr[\mu_1 = 1] < (\mu^0_1 - \mu^0_2)/2$. Pick any $\alpha > 0$ such that $\Pr[\mu_1 \ge 1 - 2\alpha] \le (\mu^0_1 - \mu^0_2)/2$. Then GREEDY suffers Bayesian regret
--   $$\mathbb{E}[R(T)] \ge T \cdot \Big(\frac{\alpha}{2}\,(\mu^0_1 - \mu^0_2)\,\Pr[\mu_2 > 1 - \alpha]\Big).$$
--
--   Formally: $P$ a prior supported on the finite $F \subseteq [0,1]^2$ under which the coordinates $\mu_1, \mu_2$ are independent (`iIndepFun`), $\Pr[\mu_1 = 1] < (\mu^0_1 - \mu^0_2)/2$, $\alpha > 0$ with $\Pr[\mu_1 \ge 1 - 2\alpha] \le (\mu^0_1 - \mu^0_2)/2$, $\pi$ any GREEDY policy and $T$ any horizon; then $T \cdot \frac{\alpha}{2}(\mu^0_1 - \mu^0_2)\Pr[\mu_2 > 1 - \alpha] \le \mathrm{BR}(T)$, with $\mathrm{BR}(T)$ the Bayesian regret (3.1) of Chapter 3 (the pseudo-regret $T\max_a \mu_a - \sum_t \mu_{a_t}$ in expectation over the run and the prior). The first hypothesis only guarantees that such an $\alpha$ exists; it is kept as printed.
-- source:
--   Slivkins, Introduction to Multi-Armed Bandits, arXiv:1904.07272 (FnT ML 12, 2019), §11.2 p. 148, Corollary 11.8 with its proof (also Exercise 11.1)

import Definitions.Def_IntroBandits_Agents

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace IntroBandits

theorem greedy_linear_bayesian_regret (P : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure P]
    (F : Finset (Fin 2 → ℝ)) (hF : P (↑F)ᶜ = 0)
    (hunit : ∀ μ ∈ F, ∀ a, μ a ∈ Set.Icc (0 : ℝ) 1) (fam : RewardFamily)
    (hindep : iIndepFun (fun (a : Fin 2) (μ : Fin 2 → ℝ) ↦ μ a) P)
    (h1 : (P {μ | μ 0 = 1}).toReal < (priorMean P F 0 - priorMean P F 1) / 2)
    {α : ℝ} (hα : 0 < α)
    (hα2 : (P {μ | 1 - 2 * α ≤ μ 0}).toReal ≤ (priorMean P F 0 - priorMean P F 1) / 2)
    {π : BanditPolicy 2} (hπ : IsGreedy P F fam π) (T : ℕ) :
    T * (α / 2 * (priorMean P F 0 - priorMean P F 1) * (P {μ | 1 - α < μ 1}).toReal) ≤
      bayesianRegret P F fam π T := by sorry

end IntroBandits
