-- Prove2me | Theorems.Thm_MostlyExplorationFree_GreedyBandit_lemma_6
-- name    : MostlyExplorationFree.GreedyBandit.lemma_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:26.456297+00:00
-- url     : https://prove2.me/theorems/24697b3f-2960-4c69-8ba2-5c4966c2d759
-- title:
--   Lemma 6, p. 16 (K = 2) — r_t ≤ 4C₀C̄x²_max(log d)^{3/2}/(C₃(t−1)) + 4b_max x_max max_i ℙ[λ_min(Σ̂(S_{i,t−1})) < λ₀(t−1)/4]
-- statement:
--   Consider the Greedy Bandit run on the two-armed linear contextual bandit with $d \ge 2$, $\sigma$-sub-Gaussian noise ($\sigma > 0$), the parameter-set assumption and the margin condition with constant $C_0$. Let $\lambda_0 > 0$, $C_3 = \lambda_0^2/(32d\sigma^2x_{\max}^2)$, let $\bar C$ be the constant of display (4), and let $\overline{\mathcal F}{}^{\lambda}_{i,t}$ be the event $\lambda_{\min}(\hat\Sigma(\mathcal S_{i,t})) < \lambda t$ (the complement of $\mathcal F^{\lambda}_{i,t}$ of display (14)). Then the instantaneous expected regret at every time $t \ge 2$ satisfies
--   $$
--   r_t \le \frac{4 C_0 \bar C x_{\max}^2 (\log d)^{3/2}}{C_3} \cdot \frac{1}{t-1} + 4 b_{\max} x_{\max} \max_{i} \mathbb P\big[\overline{\mathcal F}{}^{\lambda_0/4}_{i,t-1}\big].
--   $$
--
--   Combined with Lemma 4, which bounds the probabilities in the second term, summing this over $t$ gives Theorem 1.
--
--   **Formalization Note**
--   1. The paper states the lemma for $K$ arms with factors $4(K-1)$; here $K = 2$, the only case Theorem 1 uses, so the factor is $4$.
--   2. Covariate diversity is not assumed: $\lambda_0$ is any positive number, and the lemma holds for it (the paper notes on p. 23 that Theorem 1's proof uses Assumption 3 only through Lemma 4).
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, p. 16, Lemma 6 (restated p. 39 and proved pp. 39–42, Appendix C; events (14) p. 39), specialised to K = 2

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Model

open Matrix MeasureTheory ProbabilityTheory

namespace MostlyExplorationFree.GreedyBandit

theorem lemma_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ} (hd : 2 ≤ d)
    (μ : Measure (Fin d → ℝ)) (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ)
    (W : ℕ → Ω → Bool) (σ : ℝ) (hσ : 0 < σ) (β : Fin 2 → Fin d → ℝ)
    (xmax bmax C0 lam0 : ℝ) (hlam0 : 0 < lam0)
    (hmodel : IsGreedyModel P μ X ε W σ) (hA1 : ParameterSet μ β xmax bmax)
    (hA2 : MarginCondition μ β C0) (t : ℕ) (ht : 2 ≤ t) :
    instRegret β X ε W P t
      ≤ 4 * C0 * Cbar d * xmax ^ 2 * Real.log d ^ (3 / 2 : ℝ) / C3 lam0 d σ xmax
          * (1 / ((t : ℝ) - 1))
        + 4 * bmax * xmax *
          max (P {ω | lambdaMin (gram β X ε W 0 (t - 1) ω) < lam0 * ((t : ℝ) - 1) / 4}).toReal
              (P {ω | lambdaMin (gram β X ε W 1 (t - 1) ω) < lam0 * ((t : ℝ) - 1) / 4}).toReal := by sorry

end MostlyExplorationFree.GreedyBandit
