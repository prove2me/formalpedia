-- Prove2me | Theorems.Thm_MostlyExplorationFree_GreedyBandit_lemma_4
-- name    : MostlyExplorationFree.GreedyBandit.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:22.881704+00:00
-- url     : https://prove2.me/theorems/ec8e9d0f-3606-4b0b-9273-0f363704a0c9
-- title:
--   Lemma 4, p. 14 — under the Greedy Bandit, ℙ[λ_min(Σ̂(S_{i,t})) ≥ λ₀t/4] ≥ 1 − exp(log d − C₁t), C₁ = λ₀/(40x²_max)
-- statement:
--   Consider the Greedy Bandit run on the two-armed linear contextual bandit with $d \ge 1$, under the parameter-set assumption (contexts bounded by $x_{\max}$ in $\ell_2$) and covariate diversity with constant $\lambda_0$. Let $C_1 = \lambda_0/(40x_{\max}^2)$. Then for each arm $i$ and each time $t \ge 1$, the sample covariance matrix $\hat\Sigma(\mathcal S_{i,t}) = \sum_{s \in \mathcal S_{i,t}} X_s X_s^\top$ of that arm satisfies
--   $$
--   \mathbb P\Big[\lambda_{\min}\big(\hat\Sigma(\mathcal S_{i,t})\big) \ge \frac{\lambda_0 t}{4}\Big] \ge 1 - \exp(\log d - C_1 t).
--   $$
--
--   The greedy policy never explores deliberately, yet under covariate diversity each arm's sample covariance grows linearly in time with high probability. This is the step where Assumption 3 enters the regret analysis.
--
--   **Formalization Note** The margin condition is not assumed. Ties between the two estimates (in particular every early context, when both estimates are $0$) are broken by an independent fair coin; with a deterministic tie rule the lemma would be false.
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, p. 14, Lemma 4

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Model

open Matrix MeasureTheory ProbabilityTheory

namespace MostlyExplorationFree.GreedyBandit

theorem lemma_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ} (hd : 1 ≤ d)
    (μ : Measure (Fin d → ℝ)) (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ)
    (W : ℕ → Ω → Bool) (σ : ℝ) (β : Fin 2 → Fin d → ℝ) (xmax bmax lam0 : ℝ)
    (hmodel : IsGreedyModel P μ X ε W σ) (hA1 : ParameterSet μ β xmax bmax)
    (hA3 : CovariateDiversity μ lam0) (i : Fin 2) (t : ℕ) (ht : 1 ≤ t) :
    1 - Real.exp (Real.log d - C1 lam0 xmax * t)
      ≤ (P {ω | lam0 * t / 4 ≤ lambdaMin (gram β X ε W i t ω)}).toReal := by sorry

end MostlyExplorationFree.GreedyBandit
