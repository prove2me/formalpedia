-- Prove2me | Theorems.Thm_MemoryScreen_Menu_perfect_memory_derivative
-- name    : MemoryScreen.Menu.perfect_memory_derivative
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:42:08.857838+00:00
-- url     : https://prove2.me/theorems/4b934f6a-2632-42bd-a318-cf314b590ef5
-- title:
--   Proof of Proposition 1, p. 30 — perfect-memory derivative and sign
-- statement:
--   For the perfect-memory reduced objective $\Psi(p_H,p_L)$ of equation (4),
--
--   $$\frac{\partial\Psi}{\partial p_L}=\theta\big[F(\alpha_H-p_L)-F(\alpha_L-p_L)\big]+(1-\theta)(c-p_L)f(\alpha_L-p_L).$$
--
--   At the limited-memory price $p_L^*$, this derivative is positive exactly when $f(\alpha_L-p_L^*)$ is below the average increase of $F$ over the interval of length $\alpha_H-\alpha_L$. This is the derivative comparison behind Proposition 1.
--
--   **Formalization Note.** The derivative is multiplied out to remain defined where $f(\alpha_L-p_L)=0$; the printed quotient form has the same value wherever its denominator is positive.
-- source:
--   Guo, The Mnemonomics of Contractual Screening, SSRN preprint 3930657 (2022-03-13), p. 30 (PDF 31), proof of Proposition 1, perfect-memory first-order-derivative paragraph

import Mathlib
import Definitions.Def_MemoryScreen_Menu_Model

open MeasureTheory

namespace MemoryScreen.Menu

/-- The perfect-memory first-order derivative and its sign at the limited-memory price. -/
theorem perfect_memory_derivative (P : Params) (hS : P.Standing) :
    (∀ pH pL : ℝ,
      HasDerivAt (perfectObj P pH)
        (P.θ * (F P (P.αH - pL) - F P (P.αL - pL)) +
          (1 - P.θ) * (P.c - pL) * P.f (P.αL - pL)) pL) ∧
    (0 < deriv (perfectObj P P.c) (pStarL P) ↔
      P.f (P.αL - pStarL P) <
        (F P (P.αH - pStarL P) - F P (P.αL - pStarL P)) /
          (P.αH - P.αL)) := by sorry

end MemoryScreen.Menu
