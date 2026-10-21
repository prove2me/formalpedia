-- Prove2me | Theorems.Thm_MemoryScreen_Menu_reduced_derivatives
-- name    : MemoryScreen.Menu.reduced_derivatives
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:03.596252+00:00
-- url     : https://prove2.me/theorems/2968f1e2-e6c9-4c1a-aadd-256bd3cc3cac
-- title:
--   Proof of Proposition 1, p. 28 — reduced-objective derivatives
-- statement:
--   For the reduced objective $\Phi(p_H,p_L)$ of program (6), its partial derivatives at every pair of marginal prices are
--
--   $$\frac{\partial\Phi}{\partial p_H}=\theta(c-p_H)f(\alpha_H-p_H),\qquad\frac{\partial\Phi}{\partial p_L}=\big[(1-\theta)(c-p_L)+\theta(\alpha_H-\alpha_L)\big]f(\alpha_L-p_L).$$
--
--   These derivatives identify the candidate prices in Proposition 1. The model's continuous density makes both derivatives exist.
-- source:
--   Guo, The Mnemonomics of Contractual Screening, SSRN preprint 3930657 (2022-03-13), p. 28 (PDF 29), proof of Proposition 1, first-order-derivative display

import Mathlib
import Definitions.Def_MemoryScreen_Menu_Model

open MeasureTheory

namespace MemoryScreen.Menu

/-- The two first-order derivatives printed in the proof of Proposition 1. -/
theorem reduced_derivatives (P : Params) (hS : P.Standing) (pH pL : ℝ) :
    HasDerivAt (fun x : ℝ => reducedObj P x pL)
      (P.θ * (P.c - pH) * P.f (P.αH - pH)) pH ∧
    HasDerivAt (reducedObj P pH)
      (((1 - P.θ) * (P.c - pL) + P.θ * (P.αH - P.αL)) *
        P.f (P.αL - pL)) pL := by sorry

end MemoryScreen.Menu
