-- Prove2me | Theorems.Thm_MostlyExplorationFree_GreedyBandit_lemma_5
-- name    : MostlyExplorationFree.GreedyBandit.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:27.731763+00:00
-- url     : https://prove2.me/theorems/9c1841f5-3532-4f49-9952-f8546eec5eab
-- title:
--   Lemma 5, p. 15 — ℙ[‖β̂(S_{i,t}) − β_i‖₂ ≥ χ and λ_min(Σ̂(S_{i,t})) ≥ λt] ≤ 2d exp(−C₂t²χ²/n) for n ≥ |S_{i,t}|
-- statement:
--   Consider the Greedy Bandit run on the two-armed linear contextual bandit with $d \ge 1$, $\sigma$-sub-Gaussian noise ($\sigma > 0$) and contexts bounded by $x_{\max}$ in $\ell_2$. Fix an arm $i$, a time $t \ge 1$, and a deterministic integer $n$ with $n \ge |\mathcal S_{i,t}|$ on every outcome. For $\lambda, \chi > 0$ let $C_2 = \lambda^2/(2d\sigma^2x_{\max}^2)$. Then
--   $$
--   \mathbb P\Big[\big\|\hat\beta(\mathcal S_{i,t}) - \beta_i\big\|_2 \ge \chi \ \text{ and } \ \lambda_{\min}\big(\hat\Sigma(\mathcal S_{i,t})\big) \ge \lambda t\Big] \le 2d\exp\big(-C_2 t^2 \chi^2/n\big).
--   $$
--
--   Although the samples of arm $i$ are chosen adaptively (and so are not i.i.d.), the least-squares estimate is accurate whenever the sample covariance is well conditioned.
--
--   **Formalization Note** Neither the margin condition nor covariate diversity is assumed. Here $\hat\beta(\mathcal S_{i,t})$ and $\hat\Sigma(\mathcal S_{i,t})$ are the quantities *after* time $t$. For $n = 0$ the bound reads $2d$ because of Lean's division by zero; that case is trivial anyway, since $|\mathcal S_{i,t}| = 0$ makes the event empty.
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, p. 15, Lemma 5

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Model

open Matrix MeasureTheory ProbabilityTheory

namespace MostlyExplorationFree.GreedyBandit

theorem lemma_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ} (hd : 1 ≤ d)
    (μ : Measure (Fin d → ℝ)) (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ)
    (W : ℕ → Ω → Bool) (σ : ℝ) (hσ : 0 < σ) (β : Fin 2 → Fin d → ℝ) (xmax bmax : ℝ)
    (hmodel : IsGreedyModel P μ X ε W σ) (hA1 : ParameterSet μ β xmax bmax)
    (i : Fin 2) (t : ℕ) (ht : 1 ≤ t) (lam χ : ℝ) (hlam : 0 < lam) (hχ : 0 < χ)
    (n : ℕ) (hn : ∀ ω, (played β X ε W i t ω).card ≤ n) :
    (P {ω | χ ≤ l2norm (est β X ε W i t ω - β i) ∧
        lam * t ≤ lambdaMin (gram β X ε W i t ω)}).toReal
      ≤ 2 * d * Real.exp (-(C2 lam d σ xmax * t ^ 2 * χ ^ 2 / n)) := by sorry

end MostlyExplorationFree.GreedyBandit
