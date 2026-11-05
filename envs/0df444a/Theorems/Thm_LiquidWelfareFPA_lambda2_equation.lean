-- Prove2me | Theorems.Thm_LiquidWelfareFPA_lambda2_equation
-- name    : LiquidWelfareFPA.lambda2_equation
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T05:32:33.646197+00:00
-- url     : https://prove2.me/theorems/2dbaada8-7bdf-4340-a836-5c6917cb6d93
-- title:
--   Proof of Theorem 4.2, p.10 — $1+1/\lambda_2=\gamma/(c(\lambda_2)\lambda_2)$ (the final $\ge$ of the display is milestone (12))
-- statement:
--   For every $\gamma\ge1$, the multiplier $\lambda_2=\gamma W(-e^{-2/\gamma}/\gamma)+1$ solves $1+1/\lambda=\gamma/(c(\lambda)\lambda)$:
--
--   $$1+\frac1{\lambda_2}\ =\ \frac{\gamma}{c(\lambda_2)\lambda_2}\ =\ 1+\frac1{\gamma W\!\left(-\frac{e^{-2/\gamma}}{\gamma}\right)+1}.$$
--
--   The display on p.10 ends with "$\ge\gamma\lambda_2/(1-\lambda_2)$"; that inequality is the companion item (12) (`eq_12`), stated for $\gamma\ge\gamma_0$.
--
--   Differences from the source:
--   - generalization: for γ ≥ 1.73 → for every γ ≥ 1; reason: the identity holds for every γ ≥ 1; restricting to γ ≥ 1.73 gives the printed claim
-- source:
--   Fikioris & Tardos, Liquid Welfare Guarantees for No-Regret Learning in Sequential Budgeted Auctions, arXiv:2210.07502v4, proof of Theorem 4.2, p.10

import Mathlib
import Definitions.Def_LiquidWelfareFPA_lam2
import Definitions.Def_LiquidWelfareFPA_cfun

namespace LiquidWelfareFPA

/-- **`λ₂` solves `1 + 1/λ = γ/(c(λ)λ)`.**
Fikioris & Tardos, arXiv:2210.07502v4, proof of Theorem 4.2, p.10: "we solve the equation
1 + 1/λ = γ/(c(λ)λ), set λ2 = γW(−e^{−2/γ}/γ) + 1 … and get 1 + 1/λ2 = γ/(c(λ2)λ2) =
1 + 1/(γW(−e^{−2/γ}/γ) + 1)".

For every `γ ≥ 1`: `1 + 1/λ₂ = γ/(c(λ₂)λ₂) = 1 + 1/(γW(−e^{−2/γ}/γ) + 1)`.

**Formalization Note** The display's final "≥ γλ2/(1 − λ2)" holds only for `γ ≥ γ₀`; it is the
separate milestone (12). -/
theorem lambda2_equation (γ : ℝ) (hγ : 1 ≤ γ) :
    1 + 1 / lam2 γ = γ / (cfun (lam2 γ) * lam2 γ) ∧
      γ / (cfun (lam2 γ) * lam2 γ) = 1 + 1 / (γ * lambertW (-Real.exp (-2 / γ) / γ) + 1) := by sorry

end LiquidWelfareFPA
