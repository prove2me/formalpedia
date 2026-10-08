-- Prove2me | Theorems.Thm_L0BnB_DualGap_eq_14
-- name    : L0BnB.DualGap.eq_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T01:28:05.522982+00:00
-- url     : https://prove2.me/theorems/775a441e-28b0-4297-9ce2-7c679ac113cc
-- title:
--   (14) — closed-form solution of the coordinate problem (13) when √(λ0/λ2) ≤ M
-- statement:
--   Let $\lambda_0,\lambda_2,M>0$ with $\sqrt{\lambda_0/\lambda_2}\le M$, so that the penalty is $\psi=\psi_1$, and let $\tilde\beta_i\in\mathbb R$. Then the problem
--   $$
--   \min_{\beta_i\in\mathbb R}\ \tfrac12(\beta_i-\tilde\beta_i)^2+\psi(\beta_i;\lambda_0,\lambda_2,M)\quad\text{s.t.}\quad|\beta_i|\le M \qquad(13)
--   $$
--   has the unique solution
--   $$
--   \hat\beta_i=\begin{cases}T\big(\tilde\beta_i;\,2\sqrt{\lambda_0\lambda_2},\,M\big) & \text{if } |\tilde\beta_i|\le 2\sqrt{\lambda_0\lambda_2}+\sqrt{\lambda_0/\lambda_2},\\ T\big(\tilde\beta_i(1+2\lambda_2)^{-1};\,0,\,M\big) & \text{otherwise,}\end{cases}
--   $$
--   where $T$ is the boxed soft-thresholding operator.
--
--   This is the closed-form update of cyclic coordinate descent (Algorithm 1) in the reverse-Huber regime.
--
--   **Formalization Note** "The solution" is stated as: the given value is feasible and every other feasible point has a strictly larger objective.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 10, (14); derivation in App. B.1, p. 34

import Mathlib
import Definitions.Def_L0BnB_DualGap_Setup

namespace L0BnB.DualGap

/-- (14), p. 10 (derivation App. B.1, p. 34): for `√(λ₀/λ₂) ≤ M`, the solution of (13) is
`T(β̃ᵢ; 2√(λ₀λ₂), M)` if `|β̃ᵢ| ≤ 2√(λ₀λ₂) + √(λ₀/λ₂)` and `T(β̃ᵢ(1 + 2λ₂)⁻¹; 0, M)` otherwise. -/
theorem eq_14 (lam0 lam2 M : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hM : 0 < M)
    (hreg : Real.sqrt (lam0 / lam2) ≤ M) (bt : ℝ) :
    IsSolution13 lam0 lam2 M bt
      (if |bt| ≤ 2 * Real.sqrt (lam0 * lam2) + Real.sqrt (lam0 / lam2) then
        boxedSoftThreshold bt (2 * Real.sqrt (lam0 * lam2)) M
      else boxedSoftThreshold (bt * (1 + 2 * lam2)⁻¹) 0 M) := by sorry

end L0BnB.DualGap
