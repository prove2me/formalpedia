-- Prove2me | Theorems.Thm_MeanFieldLQ_Feedback_theorem_3_2
-- name    : MeanFieldLQ.Feedback.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:35:35.456959+00:00
-- url     : https://prove2.me/theorems/1d025cc4-0860-4c8a-a19f-cd269f3cfddf
-- title:
--   Theorem 3.2, p. 2821 — sufficiency: an adapted solution of the MF-FBSDE (3.3) gives an optimal pair
-- statement:
--   Assume (H1)–(H2). Let $(X^*,u^*,Y,Z)$ be an adapted solution of the MF-FBSDE (3.3) with initial state $x$:
--   $$\begin{cases}
--   dX^*=(AX^*+\bar A\,\mathbb E[X^*]+Bu^*+\bar B\,\mathbb E[u^*])ds+(CX^*+\bar C\,\mathbb E[X^*]+Du^*+\bar D\,\mathbb E[u^*])dW,\\
--   dY=-(A^TY+\bar A^T\mathbb E[Y]+C^TZ+\bar C^T\mathbb E[Z]+QX^*+\bar Q\,\mathbb E[X^*])ds+Z\,dW,\\
--   X^*(0)=x,\quad Y(T)=GX^*(T)+\bar G\,\mathbb E[X^*(T)],\\
--   Ru^*+\bar R\,\mathbb E[u^*]+B^TY+\bar B^T\mathbb E[Y]+D^TZ+\bar D^T\mathbb E[Z]=0 .
--   \end{cases}$$
--   Then $(X^*,u^*)$ is an optimal pair of Problem (MF-LQ) for $x$.
--
--   Together with Theorem 3.1 this shows that the optimality system characterizes the optimal pairs.
-- source:
--   Yong, Linear-Quadratic Optimal Control Problems for Mean-Field Stochastic Differential Equations, SIAM J. Control Optim. 51(4) (2013), p. 2821, Theorem 3.2 (with (3.3), p. 2820)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_MeanFieldLQ_Feedback_Setting

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal

namespace MeanFieldLQ.Feedback

/-- Theorem 3.2 (p. 2821): under (H1)–(H2), if `(X*, u*, Y, Z)` is an adapted solution of the
MF-FBSDE (3.3) with initial state `x`, then `(X*, u*)` is an optimal pair of Problem (MF-LQ). -/
theorem theorem_3_2 {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [μ.IsComplete] {W : ℝ≥0 → Ω → Fin 1 → ℝ} (hW : Peng1990.SMP.IsStdBrownian μ W)
    (T : ℝ≥0) (hT : 0 < T) (d : Data n m)
    (δ : ℝ) (h1 : H1 T d) (h2 : H2 T δ d) (x : Fin n → ℝ)
    (XStar : ℝ≥0 → Ω → Fin n → ℝ) (uStar : ℝ≥0 → Ω → Fin m → ℝ)
    (Y Z : ℝ≥0 → Ω → Fin n → ℝ) (hsol : IsFBSDESol μ hW T d x XStar uStar Y Z) :
    IsOptimalPair μ hW T d x uStar XStar := by sorry

end MeanFieldLQ.Feedback
