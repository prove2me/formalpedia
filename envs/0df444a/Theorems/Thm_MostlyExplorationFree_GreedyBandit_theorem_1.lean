-- Prove2me | Theorems.Thm_MostlyExplorationFree_GreedyBandit_theorem_1
-- name    : MostlyExplorationFree.GreedyBandit.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:32:30.967562+00:00
-- url     : https://prove2.me/theorems/72ecea2a-e3b0-4768-b818-a492b40c32e0
-- title:
--   Theorem 1, p. 12 — under covariate diversity the two-armed Greedy Bandit has R_T ≤ A log T + A + 160 b_max x³_max d/λ₀ + 2x_max b_max
-- statement:
--   Consider the Greedy Bandit (Algorithm 1) on the two-armed linear contextual bandit in dimension $d \ge 2$, with $\sigma$-sub-Gaussian noise ($\sigma > 0$), under Assumption 1 (contexts bounded by $x_{\max}$ and parameters by $b_{\max}$ in $\ell_2$), Assumption 2 (margin condition with constant $C_0$) and Assumption 3 (covariate diversity with constant $\lambda_0$). Let
--   $$
--   \bar C = \frac13 + \frac72(\log d)^{-1/2} + \frac{38}{3}(\log d)^{-1} + \frac{67}{4}(\log d)^{-3/2}, \qquad A = \frac{128 C_0 \bar C x_{\max}^4 \sigma^2 d (\log d)^{3/2}}{\lambda_0^2}.
--   $$
--   Then for every horizon $T \ge 3$ the cumulative expected regret satisfies
--   $$
--   R_T \le A \log T + \Big(A + \frac{160\, b_{\max} x_{\max}^3 d}{\lambda_0} + 2 x_{\max} b_{\max}\Big).
--   $$
--
--   In particular $R_T = O(\log T)$: an algorithm that never explores attains the optimal logarithmic regret rate of the two-armed contextual bandit once the context distribution is diverse enough. This is the paper's main result.
--
--   **Formalization Note**
--   1. The bound is the one the proof establishes (p. 42). The printed display (3) also multiplies $160b_{\max}x_{\max}^3d/\lambda_0 + 2x_{\max}b_{\max}$ by $\bar C$, which the proof never produces; whenever $\bar C \ge 1$ (every $d$ with $\log d \le 64$) the bound stated here is at least as strong as (3). The consequence "$\le C_{GB}\log T$" follows at once from $\log T \ge 1$ for $T \ge 3$ and is not restated.
--   2. $d \ge 2$ is assumed because $\bar C$ divides by $\log d$ (the paper's own range $\bar C \in (1/3, 52)$ needs it); $\sigma > 0$ because $C_2, C_3$ divide by $\sigma^2$.
--   3. Noise sub-Gaussianity is two-sided and the context law need not have a density; see the model definition.
-- source:
--   Bastani, Bayati & Khosravi, arXiv:1704.09011v8, p. 12, Theorem 1 and display (4) (bound in the form proved on p. 42, Appendix C)

import Mathlib
import Definitions.Def_MostlyExplorationFree_GreedyBandit_Model

open Matrix MeasureTheory ProbabilityTheory

namespace MostlyExplorationFree.GreedyBandit

theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) {d : ℕ} (hd : 2 ≤ d)
    (μ : Measure (Fin d → ℝ)) (X : ℕ → Ω → Fin d → ℝ) (ε : Fin 2 → ℕ → Ω → ℝ)
    (W : ℕ → Ω → Bool) (σ : ℝ) (hσ : 0 < σ) (β : Fin 2 → Fin d → ℝ)
    (xmax bmax C0 lam0 : ℝ)
    (hmodel : IsGreedyModel P μ X ε W σ) (hA1 : ParameterSet μ β xmax bmax)
    (hA2 : MarginCondition μ β C0) (hA3 : CovariateDiversity μ lam0)
    (T : ℕ) (hT : 3 ≤ T) :
    regret β X ε W P T
      ≤ 128 * C0 * Cbar d * xmax ^ 4 * σ ^ 2 * d * Real.log d ^ (3 / 2 : ℝ) / lam0 ^ 2
          * Real.log T
        + (128 * C0 * Cbar d * xmax ^ 4 * σ ^ 2 * d * Real.log d ^ (3 / 2 : ℝ) / lam0 ^ 2
          + 160 * bmax * xmax ^ 3 * d / lam0 + 2 * xmax * bmax) := by sorry

end MostlyExplorationFree.GreedyBandit
