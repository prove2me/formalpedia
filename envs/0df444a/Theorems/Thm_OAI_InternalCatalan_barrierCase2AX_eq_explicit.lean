-- Prove2me | Theorems.Thm_OAI_InternalCatalan_barrierCase2AX_eq_explicit
-- name    : OAI.InternalCatalan.barrierCase2AX_eq_explicit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-07T20:47:00.643601+00:00
-- url     : https://prove2.me/theorems/e3b7f45d-702b-43e5-9789-891531efac25
-- title:
--   OpenAI Catalan, §7.2 Eq. (93) — the derivative numerator A_X of X₂ equals its explicit degree-36 form
-- statement:
--   Let $A_X\in\mathbb Q[x]$ be the derivative numerator of the case-$\kappa=2$ barrier function $X_2$, defined in the bundle `OAICatalanBarrierPolynomials` as the numerator of the sum of the rational-function terms of $X_2'$ over the product of their denominators (`barrierCase2AX`), and let $A_X^{\mathrm{expl}}$ be the explicit polynomial with $37$ rational coefficients in the same bundle (`barrierCase2AXExplicit`). Then
--
--   $$A_X=A_X^{\mathrm{expl}}.$$
--
--   This is the exact computation of the numerator of Eq. (93), on which the root-count certificate (Eq. (94), (95)) for the stationary points of $X_2$ operates.
--
--   OpenAI, p. 37: “These equations, the coefficient tables, and $T_0=1$, $T_1=x$, $U_0=1$, $U_1=2x$, with recurrence $V_{k+1}=2xV_k-V_{k-1}$, specify the four polynomials over $\mathbb Q$ without any numerical root calculation.”
--
--   **Formalization note.** The identity is an equality of polynomials over $\mathbb Q$. Source: OpenAI, *Catalan's constant is irrational*, OpenAI Math Release, September 24, 2026, [github.com/openai/math](https://github.com/openai/math) (Apache License 2.0).
-- source:
--   OpenAI, Catalan's constant is irrational, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (paper: https://github.com/openai/math/blob/main/preprints/Catalans-constant-is-irrational-September-24-2026/paper.pdf; Lean: lean/OAI/NumberTheory/Catalan, Apache License 2.0), p. 36-37, §7.2, Eq. (93), the derivative numerator A_X

import Mathlib
import Definitions.Def_OAICatalanIrrationality
import Definitions.Def_OAICatalanBarrierPolynomials

namespace OAI.InternalCatalan

open Polynomial

theorem barrierCase2AX_eq_explicit : barrierCase2AX = barrierCase2AXExplicit := by
  sorry

end OAI.InternalCatalan
