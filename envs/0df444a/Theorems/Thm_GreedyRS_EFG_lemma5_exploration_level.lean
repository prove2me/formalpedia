-- Prove2me | Theorems.Thm_GreedyRS_EFG_lemma5_exploration_level
-- name    : GreedyRS.EFG.lemma5_exploration_level
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:35.361092+00:00
-- url     : https://prove2.me/theorems/157e1eca-b970-4d69-8dbb-0c1a97b34292
-- title:
--   Lemma 5, p. 24 — for γ₀ > 0 and α ∈ (0,1) some n₀ ≥ 1 gives Pr{min_{n≥n₀} X̄₁(n) > μ₁ − γ₀} ≥ α
-- statement:
--   Let $X_{11}, X_{12}, \dots$ be the independent $N(\mu_1, \sigma_1^2)$ observations of the best alternative ($\sigma_1^2 > 0$) and $\bar X_1(n)$ their running average. For any fixed $\gamma_0 > 0$ and any $\alpha \in (0,1)$ there is a finite $n_0 \ge 1$, which may depend on $\gamma_0$ and $\alpha$, such that
--   $$\Pr\Big\{\min_{n\ge n_0}\bar X_1(n) > \mu_1-\gamma_0\Big\} \ge \alpha. \tag{5.3}$$
--
--   This chooses the exploration size of the EFG procedure so that the lower bound of Theorem 3 reaches any prescribed level $\alpha$.
--
--   **Formalization Note** Stated inside the full observation model of the mission (only the best alternative's row matters). "$\min_{n\ge n_0}\bar X_1(n) > a$" means the path is bounded below from $n_0$ on and its infimum exceeds $a$. Only the existence of $n_0$ is asserted, as in the paper.
-- source:
--   Li, Fan & Hong, The (Surprising) Sample Optimality of Greedy Procedures for Large-Scale Ranking and Selection, arXiv:2303.02951v3, p. 24, Lemma 5, Equation (5.3)

import Mathlib
import Definitions.Def_GreedyRS_EFG_Setting

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal

namespace GreedyRS.EFG

theorem lemma5_exploration_level {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (μ : ℕ → ℝ) (v : ℕ → ℝ≥0) (X : ℕ → ℕ → Ω → ℝ)
    (hX : GreedyRS.Greedy.NormalArray P μ v X) (hv : ∀ i, 0 < v i) :
    ∀ γ0 : ℝ, 0 < γ0 → ∀ α ∈ Set.Ioo (0 : ℝ) 1, ∃ n0 : ℕ, 1 ≤ n0 ∧
      ENNReal.ofReal α ≤ P {ω | GreedyRS.Greedy.AboveFrom (GreedyRS.Greedy.runMean (fun i j => X i j ω) 0) n0 (μ 0 - γ0)} := by sorry

end GreedyRS.EFG
