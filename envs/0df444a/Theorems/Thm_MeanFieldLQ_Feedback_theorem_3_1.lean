-- Prove2me | Theorems.Thm_MeanFieldLQ_Feedback_theorem_3_1
-- name    : MeanFieldLQ.Feedback.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:35:32.476875+00:00
-- url     : https://prove2.me/theorems/ed209cd5-b24a-4ee7-ac3a-49da5e2fad9e
-- title:
--   Theorem 3.1, p. 2819 — necessary condition: the MF-BSDE (3.1) is uniquely solvable and the stationarity condition (3.2) holds
-- statement:
--   Assume (H1)–(H2). Let $(X^*,u^*)$ be an optimal pair of Problem (MF-LQ) for the initial state $x$. Then the mean-field backward SDE
--   $$dY=-\big(A^TY+\bar A^T\mathbb E[Y]+C^TZ+\bar C^T\mathbb E[Z]+QX^*+\bar Q\,\mathbb E[X^*]\big)ds+Z\,dW,\qquad Y(T)=GX^*(T)+\bar G\,\mathbb E[X^*(T)],$$
--   has an adapted solution $(Y,Z)$ such that
--   $$R u^*+\bar R\,\mathbb E[u^*]+B^TY+\bar B^T\mathbb E[Y]+D^TZ+\bar D^T\mathbb E[Z]=0\qquad ds\otimes d\mathbb P\text{-a.e. on }[0,T]\times\Omega .$$
--   The adapted solution is unique: any two solutions have the same $Y(t)$ almost surely for every $t\in[0,T]$, and the same $Z$ $ds\otimes d\mathbb P$-a.e.
--
--   This is the Pontryagin-type maximum principle for the mean-field LQ problem.
--
--   **Formalization Note.** The page writes (3.2) "for $s\in[0,T]$, a.s.". For progressive processes this is the $ds\otimes d\mathbb P$-a.e. statement up to the choice of version, and that is the form used here.
-- source:
--   Yong, Linear-Quadratic Optimal Control Problems for Mean-Field Stochastic Differential Equations, SIAM J. Control Optim. 51(4) (2013), p. 2819, Theorem 3.1, (3.1)–(3.2)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_MeanFieldLQ_Feedback_Setting

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal

namespace MeanFieldLQ.Feedback

/-- Theorem 3.1 (p. 2819): under (H1)–(H2), if `(X*, u*)` is an optimal pair for `x`, the MF-BSDE
(3.1) driven by `X*` has an adapted solution `(Y, Z)` satisfying the stationarity condition (3.2),
and its adapted solution is unique (`Y` at every `t ∈ [0, T]` a.s., `Z` `ds ⊗ dP`-a.e.). -/
theorem theorem_3_1 {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [μ.IsComplete] {W : ℝ≥0 → Ω → Fin 1 → ℝ} (hW : Peng1990.SMP.IsStdBrownian μ W)
    (T : ℝ≥0) (hT : 0 < T) (d : Data n m)
    (δ : ℝ) (h1 : H1 T d) (h2 : H2 T δ d) (x : Fin n → ℝ)
    (uStar : ℝ≥0 → Ω → Fin m → ℝ) (XStar : ℝ≥0 → Ω → Fin n → ℝ)
    (hopt : IsOptimalPair μ hW T d x uStar XStar) :
    (∃ Y Z : ℝ≥0 → Ω → Fin n → ℝ,
        IsMFBSDE μ hW T d XStar Y Z ∧ Stationary μ T d uStar Y Z) ∧
      ∀ Y Z Y' Z' : ℝ≥0 → Ω → Fin n → ℝ,
        IsMFBSDE μ hW T d XStar Y Z → IsMFBSDE μ hW T d XStar Y' Z' →
          (∀ t ≤ T, Y t =ᵐ[μ] Y' t) ∧ AEEqOn μ T Z Z' := by sorry

end MeanFieldLQ.Feedback
