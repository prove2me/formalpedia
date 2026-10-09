-- Prove2me | Theorems.Thm_MeanFieldLQ_Feedback_proposition_2_6
-- name    : MeanFieldLQ.Feedback.proposition_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:35:36.88807+00:00
-- url     : https://prove2.me/theorems/fd5164f3-48a1-4a7a-a7da-99cbd05f8bc6
-- title:
--   Proposition 2.6, p. 2817 — the mean-field state equation (1.1) is well posed in 𝒳̂[0, T]
-- statement:
--   Assume (H1). Let $x\in\mathbb R^n$ and let $u\in\mathcal U[0,T]$ be an admissible control. Then the mean-field state equation
--   $$dX=\big(AX+\bar A\,\mathbb E[X]+Bu+\bar B\,\mathbb E[u]\big)ds+\big(CX+\bar C\,\mathbb E[X]+Du+\bar D\,\mathbb E[u]\big)dW,\qquad X(0)=x,$$
--   has a solution $X$ in $\widehat{\mathcal X}[0,T]$, i.e. with almost surely continuous paths on $[0,T]$ and $\mathbb E\sup_{s\in[0,T]}|X(s)|^2<\infty$. Any two solutions $X,X'$ satisfy $X(t)=X'(t)$ almost surely for every $t\in[0,T]$.
--
--   This defines the state map $u\mapsto X(\cdot\,;x,u)$ on which the cost functional and the whole control problem rest.
--
--   **Formalization Note.** Uniqueness is stated among all solutions in the solution class of the published SDE notion. That class (progressive, $\sup_{t\le T}\mathbb E|X(t)|^2<\infty$) contains $\widehat{\mathcal X}[0,T]$, so this uniqueness is at least the paper's. The complete probability space and $T>0$ are the paper's standing conventions.
-- source:
--   Yong, Linear-Quadratic Optimal Control Problems for Mean-Field Stochastic Differential Equations, SIAM J. Control Optim. 51(4) (2013), p. 2817, Proposition 2.6

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_MeanFieldLQ_Feedback_Setting

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal

namespace MeanFieldLQ.Feedback

/-- Proposition 2.6 (p. 2817): under (H1), for every `(x, u) ∈ ℝⁿ × 𝒰[0, T]` the state equation
(1.1) has a solution in `𝒳̂[0, T]`, and any two solutions agree at every `t ∈ [0, T]` almost
surely. -/
theorem proposition_2_6 {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [μ.IsComplete] {W : ℝ≥0 → Ω → Fin 1 → ℝ} (hW : Peng1990.SMP.IsStdBrownian μ W)
    (T : ℝ≥0) (hT : 0 < T) (d : Data n m)
    (h1 : H1 T d) (x : Fin n → ℝ) (u : ℝ≥0 → Ω → Fin m → ℝ)
    (hu : Peng1990.SMP.L2F (filt μ hW) μ T u) :
    (∃ X : ℝ≥0 → Ω → Fin n → ℝ, IsState μ hW T d x u X ∧ InXhat μ T X) ∧
      ∀ X X' : ℝ≥0 → Ω → Fin n → ℝ, IsState μ hW T d x u X → IsState μ hW T d x u X' →
        ∀ t ≤ T, X t =ᵐ[μ] X' t := by sorry

end MeanFieldLQ.Feedback
