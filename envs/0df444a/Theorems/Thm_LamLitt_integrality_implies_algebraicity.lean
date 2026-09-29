-- Prove2me | Theorems.Thm_LamLitt_integrality_implies_algebraicity
-- name    : LamLitt.integrality_implies_algebraicity
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T16:42:16.369564+00:00
-- url     : https://prove2.me/theorems/d67a689e-5b1e-4766-a56d-2acf8b0f6be8
-- title:
--   Lam–Litt: bounded denominators imply algebraicity (Litt's problem 1)
-- statement:
--   Let $n\ge0$, $g\in\mathbb{Q}(z,y_0,\dots,y_{n-1})$ and let $f=\sum_k a_kz^k\in\mathbb{Q}[[z]]$ satisfy $f^{(n)}=g(z,f,\dots,f^{(n-1)})$ with $g(0,f(0),\dots,f^{(n-1)}(0))$ defined. If there is $N$ with $a_k\in\mathbb{Z}[1/N]$ for all $k$, then
--   $$f\ \text{is algebraic over}\ \mathbb{Q}[z].$$
--
--   This is the implication (2)⇒(1) of the Lam–Litt conjecture, the version posed as Problem 1 on Litt's problem list. It is open.
--
--   **Formalization Note** The ODE hypothesis is `IsSolutionOfAlgebraicODE`, as in the goal theorem.
-- source:
--   Formal Conjectures, FormalConjectures/LittProblems/1.lean (Lam--Litt conjecture); Y. H. J. Lam, D. Litt, Algebraicity and integrality of solutions to differential equations, https://arxiv.org/abs/2501.13175; D. Litt, Problem 1, https://www.problemsilike.com/1

import Definitions.Def_LamLitt_Defs
import Mathlib

open PowerSeries

namespace LamLitt

theorem integrality_implies_algebraicity {n : ℕ} (f : PowerSeries ℚ)
    (g : MvRatFunc (Fin (n + 1)) ℚ) (hODE : IsSolutionOfAlgebraicODE n f g)
    (N : ℕ) (hN : IsCoeffIntegralAdjointInvNat f N) :
    IsAlgebraic (Polynomial ℚ) f := by sorry

end LamLitt
