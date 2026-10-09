-- Prove2me | Theorems.Thm_MeanFieldLQ_Feedback_theorem_4_1
-- name    : MeanFieldLQ.Feedback.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:36:48.343773+00:00
-- url     : https://prove2.me/theorems/a304b956-52fa-4421-86ac-cfa249d7cbd8
-- title:
--   Theorem 4.1, p. 2827 — the Riccati equations (4.8)–(4.9) are uniquely solvable, the state feedback is optimal, and inf J = ⟨Π(0)x, x⟩
-- statement:
--   Assume (H1)–(H2). Then:
--
--   1. The Riccati equation (4.8) for $P$, with $P(T)=G$, has a solution on $[0,T]$, and every solution coincides with it on $[0,T]$.
--   2. For this $P$, the Riccati equation (4.9) for $\Pi$, with $\Pi(T)=G+\bar G$, has a solution on $[0,T]$, unique on $[0,T]$.
--   3. For every $x\in\mathbb R^n$ the closed-loop system
--   $$dX^*=\Big\{[A-BK_0](X^*-\mathbb E[X^*])+[(A+\bar A)-(B+\bar B)K_1]\mathbb E[X^*]\Big\}dt+\Big\{[C-DK_0](X^*-\mathbb E[X^*])+[(C+\bar C)-(D+\bar D)K_1]\mathbb E[X^*]\Big\}dW,$$
--   with $X^*(0)=x$, has a solution in $\widehat{\mathcal X}[0,T]$. Any two solutions agree almost surely at every $t\in[0,T]$. Here $K_0=\Sigma_0^{-1}(B^TP+D^TPC)$, $K_1=\Sigma_1^{-1}[(B+\bar B)^T\Pi+(D+\bar D)^TP(C+\bar C)]$, $\Sigma_0=R+D^TPD$ and $\Sigma_1=R+\bar R+(D+\bar D)^TP(D+\bar D)$.
--   4. For every solution $X^*$ of the closed-loop system, define
--   $$u^*=-K_0(X^*-\mathbb E[X^*])-K_1\mathbb E[X^*],\qquad Y=P(X^*-\mathbb E[X^*])+\Pi\,\mathbb E[X^*],$$
--   $$Z=[PC-PDK_0](X^*-\mathbb E[X^*])+[P(C+\bar C)-P(D+\bar D)K_1]\mathbb E[X^*].$$
--   Then $(X^*,u^*,Y,Z)$ is an adapted solution of the MF-FBSDE (3.3), and $(X^*,u^*)$ is an optimal pair of Problem (MF-LQ).
--   5. The value is given by (4.10):
--   $$\inf_{u\in\mathcal U[0,T]}J(x;u)=\langle\Pi(0)x,x\rangle\qquad\forall x\in\mathbb R^n,$$
--   in the form $\langle\Pi(0)x,x\rangle\le J(x;u)$ for every admissible $u$, with equality at $u^*$.
--
--   The theorem represents the optimal control of the mean-field LQ problem as a feedback of the state and of its mean, through two Riccati equations, and gives the optimal value in closed form.
--
--   **Formalization Note.** Riccati solutions are taken in integral form. The class of (4.8) is the regular class $\Sigma_0\ge\varepsilon I$. Solutions of (4.9) are continuous and symmetric. The value (4.10) is stated as a lower bound attained at $u^*$, not as an infimum over a set of reals, which avoids the junk value of `sInf`. Since $P$ and $\Pi$ are determined on $[0,T]$ only, the statement asserts the existence of solutions $P$, $\Pi$ (their values after $T$ are irrelevant to the problem) for which items 3–5 hold. The standing assumptions are those of the definition file.
-- source:
--   Yong, Linear-Quadratic Optimal Control Problems for Mean-Field Stochastic Differential Equations, SIAM J. Control Optim. 51(4) (2013), p. 2827, Theorem 4.1 and (4.10)

import Mathlib
import Definitions.Def_Peng1990_SMP_Stochastic
import Definitions.Def_ReflectedBSDE_Existence_Setting
import Definitions.Def_MeanFieldLQ_Feedback_Setting
import Definitions.Def_MeanFieldLQ_Feedback_Riccati

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal

namespace MeanFieldLQ.Feedback

/-- Theorem 4.1 (p. 2827): under (H1)–(H2), the Riccati equations (4.8) and (4.9) have solutions
`P` and `Π` on `[0, T]`, each unique on `[0, T]` in its class; for every `x ∈ ℝⁿ` the closed-loop
system has a solution `X*` in `𝒳̂[0, T]`, unique at every `t ∈ [0, T]` a.s.; for every closed-loop
solution `X*`, with `u* = −K₀(X* − 𝔼[X*]) − K₁𝔼[X*]`, `Y = P(X* − 𝔼[X*]) + Π𝔼[X*]` and
`Z = [PC − PDK₀](X* − 𝔼[X*]) + [P(C + C̄) − P(D + D̄)K₁]𝔼[X*]`, the 4-tuple `(X*, u*, Y, Z)` is an
adapted solution of the MF-FBSDE (3.3), `(X*, u*)` is an optimal pair, and (4.10) holds:
`⟨Π(0)x, x⟩ ≤ J(x; u)` for every admissible `u` with its state, with equality at `u*`. -/
theorem theorem_4_1 {n m : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    [μ.IsComplete] {W : ℝ≥0 → Ω → Fin 1 → ℝ} (hW : Peng1990.SMP.IsStdBrownian μ W)
    (T : ℝ≥0) (hT : 0 < T) (d : Data n m)
    (δ : ℝ) (h1 : H1 T d) (h2 : H2 T δ d) :
    ∃ P Pi : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ,
      IsRiccatiP T d P ∧
      (∀ P' : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ, IsRiccatiP T d P' → ∀ s ≤ T, P' s = P s) ∧
      IsRiccatiPi T d P Pi ∧
      (∀ Pi' : ℝ≥0 → Matrix (Fin n) (Fin n) ℝ, IsRiccatiPi T d P Pi' → ∀ s ≤ T, Pi' s = Pi s) ∧
      ∀ x : Fin n → ℝ,
        (∃ XStar : ℝ≥0 → Ω → Fin n → ℝ,
            IsClosedLoop μ hW T d P Pi x XStar ∧ InXhat μ T XStar) ∧
        (∀ X X' : ℝ≥0 → Ω → Fin n → ℝ,
            IsClosedLoop μ hW T d P Pi x X → IsClosedLoop μ hW T d P Pi x X' →
              ∀ t ≤ T, X t =ᵐ[μ] X' t) ∧
        ∀ XStar : ℝ≥0 → Ω → Fin n → ℝ, IsClosedLoop μ hW T d P Pi x XStar →
          IsFBSDESol μ hW T d x XStar (feedbackU μ d P Pi XStar) (adjY μ P Pi XStar)
              (adjZ μ d P Pi XStar) ∧
            IsOptimalPair μ hW T d x (feedbackU μ d P Pi XStar) XStar ∧
            (∀ (u : ℝ≥0 → Ω → Fin m → ℝ) (X : ℝ≥0 → Ω → Fin n → ℝ),
              Peng1990.SMP.L2F (filt μ hW) μ T u → IsState μ hW T d x u X →
                (Pi 0 *ᵥ x) ⬝ᵥ x ≤ cost μ T d u X) ∧
            cost μ T d (feedbackU μ d P Pi XStar) XStar = (Pi 0 *ᵥ x) ⬝ᵥ x := by sorry

end MeanFieldLQ.Feedback
