-- Prove2me | Theorems.Thm_InfoRelaxTS_Monotone_WTS_ge_WFH
-- name    : InfoRelaxTS.Monotone.WTS_ge_WFH
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:11.987377+00:00
-- url     : https://prove2.me/theorems/64deeeb6-e4c1-4d79-a804-035d97a4628e
-- title:
--   (124), §D.3.1, p. 56 — W^TS(T, y) ≥ W^IRS.FH(T, y)
-- statement:
--   The model is the Bayesian bandit of §2.1: arms $a \in \mathcal A = \{1,\dots,K\}$ (0-based in Lean, $K \ge 1$), reward laws $\mathcal R_a(\theta_a)$, conjugate priors $\mathcal P_a(y_a)$, the Bayesian update $\mathcal U_a$, and the outcome law $\mathcal I(y)$ under which the arms are independent, $\theta_a \sim \mathcal P_a(y_a)$, and the rewards of arm $a$ are i.i.d. $\mathcal R_a(\theta_a)$ given $\theta_a$. The standing assumptions of §2.1 hold: $\mathcal U_a(y_a,r)$ is the Bayes posterior after observing $r$, the update maps are measurable, and $\mathbb E_{y_a}|R_{a,1}| < \infty$ for every belief $y_a$ (3).
--
--   For every horizon $T \in \mathbb N_0$ and belief vector $y$,
--
--   $$W^{TS}(T,y) = T\,\mathbb E_y\Big[\max_a \mu_a(\theta_a)\Big] \ge T\,\mathbb E_y\Big[\max_a \hat\mu_{a,T-1}\Big] = W^{IRS.FH}(T,y).$$
--
--   This is the first inequality of (57): the IRS.FH bound, which lets the decision maker see $T-1$ rewards of every arm in advance, is no looser than the conventional regret benchmark.
--
--   **Formalization Note** $W^{IRS.FH}$ is defined by its closed form (33).
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, p. 56, §D.3.1, (124)

import Mathlib
import Definitions.Def_InfoRelaxTS_Monotone_Setting

namespace InfoRelaxTS.Monotone

open MeasureTheory ProbabilityTheory

/-- (124), §D.3.1, p. 56: `W^TS(T, y) ≥ W^{IRS.FH}(T, y)`. -/
theorem WTS_ge_WFH {K : ℕ} [NeZero K] {Θ Y : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    [Nonempty Θ] [MeasurableSpace Y]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U)
    (T : ℕ) (y : Fin K → Y) :
    WFH R P U T y ≤ WTS R P T y := by sorry

end InfoRelaxTS.Monotone
