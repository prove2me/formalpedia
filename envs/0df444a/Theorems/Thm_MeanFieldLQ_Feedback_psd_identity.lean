-- Prove2me | Theorems.Thm_MeanFieldLQ_Feedback_psd_identity
-- name    : MeanFieldLQ.Feedback.psd_identity
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:34:41.935028+00:00
-- url     : https://prove2.me/theorems/80bd51e2-8103-46f7-ac83-b80af12bdcf3
-- title:
--   §4, display after (4.7), p. 2825 — P − PD̃(R̃ + D̃ᵀPD̃)⁻¹D̃ᵀP = P^{1/2}(I + P^{1/2}D̃R̃⁻¹D̃ᵀP^{1/2})⁻¹P^{1/2} ≥ 0
-- statement:
--   Let $P\in\mathcal S^n$ be positive semidefinite with positive semidefinite square root $P^{1/2}$. Let $\widetilde D\in\mathbb R^{n\times m}$, and let $\widetilde R\in\mathcal S^m$ be positive definite. Then
--   $$P-P\widetilde D(\widetilde R+\widetilde D^TP\widetilde D)^{-1}\widetilde D^TP=P^{1/2}\big(I+P^{1/2}\widetilde D\widetilde R^{-1}\widetilde D^TP^{1/2}\big)^{-1}P^{1/2},$$
--   and this matrix is positive semidefinite.
--
--   In the paper, $\widetilde D=D+\bar D$ and $\widetilde R=R+\bar R$, so $\widetilde R+\widetilde D^TP\widetilde D=\Sigma_1$. The identity shows that the "state weight" $(C+\bar C)^T[P-P(D+\bar D)\Sigma_1^{-1}(D+\bar D)^TP](C+\bar C)+Q+\bar Q$ of the second Riccati equation is positive semidefinite.
--
--   **Formalization Note.** The square root is a hypothesis: any positive semidefinite $S$ with $S^2=P$. The positive semidefinite square root is unique, so this is the paper's $P^{1/2}$.
-- source:
--   Yong, Linear-Quadratic Optimal Control Problems for Mean-Field Stochastic Differential Equations, SIAM J. Control Optim. 51(4) (2013), p. 2825, §4, display after (4.7) (notation D̃, R̃ on p. 2826)

import Mathlib

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal ENNReal

namespace MeanFieldLQ.Feedback

/-- §4, display after (4.7) (p. 2825): for a positive semidefinite `P ∈ 𝒮ⁿ` with positive
semidefinite square root `S = P^{1/2}`, a matrix `D̃ ∈ ℝ^{n×m}` and a positive definite
`R̃ ∈ 𝒮ᵐ`,
`P − PD̃(R̃ + D̃ᵀPD̃)⁻¹D̃ᵀP = P^{1/2}(I + P^{1/2}D̃R̃⁻¹D̃ᵀP^{1/2})⁻¹P^{1/2}`, and this matrix is
positive semidefinite. -/
theorem psd_identity {n m : ℕ} (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef)
    (Dt : Matrix (Fin n) (Fin m) ℝ) (Rt : Matrix (Fin m) (Fin m) ℝ) (hR : Rt.PosDef)
    (S : Matrix (Fin n) (Fin n) ℝ) (hS : S.PosSemidef) (hSP : S * S = P) :
    P - P * Dt * (Rt + Dtᵀ * P * Dt)⁻¹ * Dtᵀ * P
        = S * (1 + S * Dt * Rt⁻¹ * Dtᵀ * S)⁻¹ * S ∧
      (P - P * Dt * (Rt + Dtᵀ * P * Dt)⁻¹ * Dtᵀ * P).PosSemidef := by sorry

end MeanFieldLQ.Feedback
