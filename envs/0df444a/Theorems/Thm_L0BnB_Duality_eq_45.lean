-- Prove2me | Theorems.Thm_L0BnB_Duality_eq_45
-- name    : L0BnB.Duality.eq_45
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T00:22:11.236135+00:00
-- url     : https://prove2.me/theorems/ff42b17c-50a9-4b80-8c2c-1131ce1cd939
-- title:
--   (45) — the minimizer of $D_i$ on $|\beta_i|\le\sqrt{\lambda_0/\lambda_2}$
-- statement:
--   Let $\lambda_0,\lambda_2>0$, let $a\in\mathbb R$ (standing for $\alpha^TX_i$) and $\eta\ge 0$ (a multiplier $\eta_i$), and let $D(b)=\psi_1(b;\lambda_0,\lambda_2)+ab+\eta|b|$. Set
--
--   $$
--   \tilde\beta=\begin{cases}0 & \text{if } 2\sqrt{\lambda_0\lambda_2}+\eta-|a|\ge 0,\\ -\sqrt{\lambda_0/\lambda_2}\,\mathrm{sign}(a) & \text{otherwise.}\end{cases}
--   $$
--
--   Then $|\tilde\beta|\le\sqrt{\lambda_0/\lambda_2}$ and
--
--   $$
--   D(\tilde\beta)\le D(b)\qquad\text{for every } b \text{ with } |b|\le\sqrt{\lambda_0/\lambda_2}.
--   $$
--
--   This is Case 1 of the inner minimization in the proof of Theorem 2: on this interval $\psi_1(b)=2\sqrt{\lambda_0\lambda_2}|b|$, so $D$ is piecewise linear.
--
--   **Formalization Note** The paper's "argmin" is stated as membership in the interval plus minimality over it; uniqueness is not claimed. $\eta\ge 0$ is the sign constraint of the multipliers in (43). sign is `Real.sign`; in the second case $|a|>2\sqrt{\lambda_0\lambda_2}>0$, so sign(0) does not arise there.
-- source:
--   Hazimeh, Mazumder, Saab, Sparse Regression at Scale: Branch-and-Bound rooted in First-Order Optimization, arXiv:2004.06152v2, p. 31, Proof of Theorem 2, Case 1, (45)

import Mathlib
import Definitions.Def_L0BnB_Duality_Dual

namespace L0BnB.Duality

/-- (45), proof of Theorem 2, p. 31 (Case 1: `|βᵢ| ≤ √(λ₀/λ₂)`). For `a = αᵀXᵢ` and `η = ηᵢ ≥ 0`,
the point `β̃*ᵢ` of (45) lies in `[−√(λ₀/λ₂), √(λ₀/λ₂)]` and minimizes
`Dᵢ(βᵢ) = ψ₁(βᵢ; λ₀, λ₂) + a βᵢ + η|βᵢ|` over that interval. -/
theorem eq_45 (lam0 lam2 a η : ℝ) (hlam0 : 0 < lam0) (hlam2 : 0 < lam2) (hη : 0 ≤ η) :
    betaTilde45 lam0 lam2 a η ∈ Set.Icc (-Real.sqrt (lam0 / lam2)) (Real.sqrt (lam0 / lam2)) ∧
      ∀ b ∈ Set.Icc (-Real.sqrt (lam0 / lam2)) (Real.sqrt (lam0 / lam2)),
        D lam0 lam2 a η (betaTilde45 lam0 lam2 a η) ≤ D lam0 lam2 a η b := by sorry

end L0BnB.Duality
