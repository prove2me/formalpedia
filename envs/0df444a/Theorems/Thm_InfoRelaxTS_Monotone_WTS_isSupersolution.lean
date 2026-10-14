-- Prove2me | Theorems.Thm_InfoRelaxTS_Monotone_WTS_isSupersolution
-- name    : InfoRelaxTS.Monotone.WTS_isSupersolution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:31:35.207686+00:00
-- url     : https://prove2.me/theorems/3300850c-6d01-4d45-a08c-b16da65e451d
-- title:
--   (176)–(180), §D.3.3, p. 62 — W^TS is a supersolution of the Bellman equation
-- statement:
--   The model is the Bayesian bandit of §2.1: arms $a \in \mathcal A = \{1,\dots,K\}$ (0-based in Lean, $K \ge 1$), reward laws $\mathcal R_a(\theta_a)$, conjugate priors $\mathcal P_a(y_a)$, the Bayesian update $\mathcal U_a$, and the outcome law $\mathcal I(y)$ under which the arms are independent, $\theta_a \sim \mathcal P_a(y_a)$, and the rewards of arm $a$ are i.i.d. $\mathcal R_a(\theta_a)$ given $\theta_a$. The standing assumptions of §2.1 hold: $\mathcal U_a(y_a,r)$ is the Bayes posterior after observing $r$, the update maps are measurable, and $\mathbb E_{y_a}|R_{a,1}| < \infty$ for every belief $y_a$ (3).
--
--   The TS bound $W^{TS}(T,y) = \mathbb E_y[T \max_a \mu_a(\theta_a)]$ is a supersolution (Definition 2): $W^{TS}(0,y) = 0$ and for all $T \ge 1$, beliefs $y$ and arms $a$,
--
--   $$W^{TS}(T,y) \ge \mathbb E_y\big[R_{a,1} + W^{TS}(T-1, \mathcal U(y,a,R_{a,1}))\big].$$
--
--   Combined with Lemma 2 this yields $W^{TS}(T,y) \ge W^{IRS.V\text{-}EMax}(T,y)$, (58).
--
--   **Formalization Note** The supersolution predicate includes that the expectation on the right exists.
-- source:
--   Min, Maglaras, Moallemi, Thompson Sampling with Information Relaxation Penalties, arXiv:1902.04251v2, p. 62, §D.3.3, (176)–(180)

import Mathlib
import Definitions.Def_InfoRelaxTS_Monotone_Setting

namespace InfoRelaxTS.Monotone

open MeasureTheory ProbabilityTheory

/-- (176)–(180), §D.3.3, p. 62: `W^TS(·, ·)` is a supersolution (Definition 2). -/
theorem WTS_isSupersolution {K : ℕ} [NeZero K] {Θ Y : Type*} [MeasurableSpace Θ] [StandardBorelSpace Θ]
    [Nonempty Θ] [MeasurableSpace Y]
    (R : Fin K → Kernel Θ ℝ) [∀ a, IsMarkovKernel (R a)]
    (P : Fin K → Kernel Y Θ) [∀ a, IsMarkovKernel (P a)]
    (U : Fin K → Y → ℝ → Y) (hM : StandingAssumptions R P U) :
    IsSupersolution R P U (fun m y' => WTS R P m y') := by sorry

end InfoRelaxTS.Monotone
