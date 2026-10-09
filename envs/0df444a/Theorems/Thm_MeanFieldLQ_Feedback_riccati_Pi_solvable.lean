-- Prove2me | Theorems.Thm_MeanFieldLQ_Feedback_riccati_Pi_solvable
-- name    : MeanFieldLQ.Feedback.riccati_Pi_solvable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:37:27.857448+00:00
-- url     : https://prove2.me/theorems/10ef20bb-6db6-4cd9-b2e6-e75fbdfa4b73
-- title:
--   §4, p. 2826 — given P ≥ 0, the Riccati equation (4.6) = (4.9) has a unique solution Π, and Π ≥ 0
-- statement:
--   Assume (H1)–(H2). Let $P$ be a solution of the first Riccati equation (4.8) with $P(s)\ge0$ on $[0,T]$, and let $\Sigma_1=R+\bar R+(D+\bar D)^TP(D+\bar D)$. Then the Riccati equation
--   $$\dot\Pi+\Pi(A+\bar A)+(A+\bar A)^T\Pi+(C+\bar C)^TP(C+\bar C)+Q+\bar Q-\big[\Pi(B+\bar B)+(C+\bar C)^TP(D+\bar D)\big]\Sigma_1^{-1}\big[(B+\bar B)^T\Pi+(D+\bar D)^TP(C+\bar C)\big]=0,$$
--   with $\Pi(T)=G+\bar G$, has a solution $\Pi$ on $[0,T]$ with $\Pi(s)\ge0$ for all $s\in[0,T]$. Any two solutions coincide on $[0,T]$.
--
--   The solution $\Pi$ governs the feedback acting on the mean $\mathbb E[X]$, and $\langle\Pi(0)x,x\rangle$ is the optimal value.
--
--   **Formalization Note.** The statement is for (4.6) = (4.9), as printed. The rewritten form (4.7) on p. 2825 has a sign slip in its second line. Its correct form is equivalent to (4.6). The page says "positive definite". This is false in general ($G=\bar G=0$, $Q=\bar Q\equiv0$ give $\Pi\equiv0$), so semidefiniteness is asserted.
-- source:
--   Yong, Linear-Quadratic Optimal Control Problems for Mean-Field Stochastic Differential Equations, SIAM J. Control Optim. 51(4) (2013), p. 2826, §4, claim after the display of conditions (recall (2.3)) on (4.7)/(4.6); (4.6) is (4.9) of Theorem 4.1

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_MeanFieldLQ_Feedback_Setting
import Definitions.Def_MeanFieldLQ_Feedback_Riccati

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal

namespace MeanFieldLQ.Feedback

/-- §4, p. 2826: under (H1)–(H2), if `P` solves (4.8) with `P(s) ≥ 0` on `[0, T]`, then the Riccati
equation (4.6) = (4.9) has a solution `Π` on `[0, T]` with `Π(s) ≥ 0` for `s ∈ [0, T]`, and any two
solutions coincide on `[0, T]`. -/
theorem riccati_Pi_solvable {n m : ℕ} (T : ℝ≥0) (hT : 0 < T) (d : Data n m) (δ : ℝ)
    (h1 : H1 T d) (h2 : H2 T δ d) (P : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ)
    (hP : IsRiccatiP T d P) (hPpsd : ∀ s ≤ T, (P s).PosSemidef) :
    (∃ Pi : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ, IsRiccatiPi T d P Pi ∧ ∀ s ≤ T, (Pi s).PosSemidef) ∧
      ∀ Pi Pi' : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ, IsRiccatiPi T d P Pi → IsRiccatiPi T d P Pi' →
        ∀ s ≤ T, Pi s = Pi' s := by sorry

end MeanFieldLQ.Feedback
