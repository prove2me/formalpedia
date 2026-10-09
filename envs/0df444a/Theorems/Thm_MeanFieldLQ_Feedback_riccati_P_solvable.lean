-- Prove2me | Theorems.Thm_MeanFieldLQ_Feedback_riccati_P_solvable
-- name    : MeanFieldLQ.Feedback.riccati_P_solvable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:36:33.569632+00:00
-- url     : https://prove2.me/theorems/d3d3319f-aefb-45e9-a445-01ddeb7f1b51
-- title:
--   §4, after (4.6), p. 2825 — the Riccati equation (4.5) = (4.8) has a unique solution P, and P ≥ 0
-- statement:
--   Assume (H1)–(H2). The Riccati differential equation
--   $$\dot P+PA+A^TP+C^TPC+Q-(PB+C^TPD)\Sigma_0^{-1}(B^TP+D^TPC)=0,\quad s\in[0,T],\qquad P(T)=G,$$
--   with $\Sigma_0=R+D^TPD$, has a solution $P$ on $[0,T]$ with $P(s)\ge0$ for all $s\in[0,T]$. Any two solutions coincide on $[0,T]$.
--
--   The solution $P$ governs the feedback acting on the deviation $X-\mathbb E[X]$, and its semidefiniteness is what makes $\Sigma_1\ge\delta I$ in the second Riccati equation.
--
--   **Formalization Note.** Solutions are taken in integral form in the regular class $\Sigma_0\ge\varepsilon I$ (see the definition file). The page says "positive definite". That is false in general: with $G=0$ and $Q\equiv0$, $P\equiv0$ is the solution. The statement asserts positive semidefiniteness.
-- source:
--   Yong, Linear-Quadratic Optimal Control Problems for Mean-Field Stochastic Differential Equations, SIAM J. Control Optim. 51(4) (2013), p. 2825, §4, after (4.6) (claim on (4.5); (4.5) is (4.8) of Theorem 4.1)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_MeanFieldLQ_Feedback_Setting
import Definitions.Def_MeanFieldLQ_Feedback_Riccati

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal

namespace MeanFieldLQ.Feedback

/-- §4, after (4.6) (p. 2825): under (H1)–(H2), the Riccati equation (4.5) = (4.8) has a solution
`P` on `[0, T]` (in the regular class `Σ₀ ≥ εI`), with `P(s) ≥ 0` for `s ∈ [0, T]`, and any two
solutions in that class coincide on `[0, T]`. -/
theorem riccati_P_solvable {n m : ℕ} (T : ℝ≥0) (hT : 0 < T) (d : Data n m) (δ : ℝ)
    (h1 : H1 T d) (h2 : H2 T δ d) :
    (∃ P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ, IsRiccatiP T d P ∧ ∀ s ≤ T, (P s).PosSemidef) ∧
      ∀ P P' : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ, IsRiccatiP T d P → IsRiccatiP T d P' →
        ∀ s ≤ T, P s = P' s := by sorry

end MeanFieldLQ.Feedback
