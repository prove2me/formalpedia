-- Prove2me | Theorems.Thm_MassartDKW_Tight_claim_1
-- name    : MassartDKW.Tight.claim_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T12:58:53.005986+00:00
-- url     : https://prove2.me/theorems/a128e4cb-3dc6-4d26-b0ea-131e0e36d1a0
-- title:
--   Claim 1, p. 1275 — (1 + 2x)^{−1/2} ≤ (1 − x + 3x²/2) exp(−βx³) on [0, 1], β = 0.826
-- statement:
--   Let $\beta=0.826$. For every $x\in[0,1]$,
--   $$(1+2x)^{-1/2}\le\Bigl(1-x+\frac{3x^2}2\Bigr)\exp(-\beta x^3).$$
--
--   It is applied with $x=\varepsilon/(3s')$ to prove Claim 2.
-- source:
--   Massart, The tight constant in the Dvoretzky–Kiefer–Wolfowitz inequality, Ann. Probab. 18 (1990), p. 1275, Claim 1

import Mathlib
import Definitions.Def_MassartDKW_Tight_Analytic

namespace MassartDKW.Tight

theorem claim_1 : ∀ x ∈ Set.Icc (0 : ℝ) 1,
    (1 + 2 * x) ^ (-(1 / 2 : ℝ)) ≤ (1 - x + 3 * x ^ 2 / 2) * Real.exp (-(0.826 * x ^ 3)) := by sorry

end MassartDKW.Tight
