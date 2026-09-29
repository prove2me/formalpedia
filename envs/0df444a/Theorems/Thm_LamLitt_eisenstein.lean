-- Prove2me | Theorems.Thm_LamLitt_eisenstein
-- name    : LamLitt.eisenstein
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T16:35:45.089904+00:00
-- url     : https://prove2.me/theorems/c7f2f12d-e257-4270-906e-cbadcbf7ff32
-- title:
--   Eisenstein's theorem: algebraic power series have bounded denominators
-- statement:
--   **Eisenstein's theorem (1852).** Let $f=\sum_{k\ge0}a_kz^k\in\mathbb{Q}[[z]]$ be algebraic over $\mathbb{Q}[z]$. Then there exists $N\ge1$ such that
--   $$a_k\in\mathbb{Z}[1/N]\qquad\text{for all }k\ge0.$$
--
--   This is the implication (1)⇒(2) of the Lam–Litt conjecture; it holds without any differential equation hypothesis.
--
--   **Formalization Note** The conclusion allows any natural number $N$; since $1/0=0$ in Lean, $N=0$ corresponds to $\mathbb{Z}[1/0]=\mathbb{Z}$, which is contained in $\mathbb{Z}[1/1]$, so this does not change the statement.
-- source:
--   Formal Conjectures, FormalConjectures/LittProblems/1.lean (Lam--Litt conjecture); Y. H. J. Lam, D. Litt, Algebraicity and integrality of solutions to differential equations, https://arxiv.org/abs/2501.13175; D. Litt, Problem 1, https://www.problemsilike.com/1

import Definitions.Def_LamLitt_Defs
import Mathlib

open PowerSeries

namespace LamLitt

theorem eisenstein (f : PowerSeries ℚ) (hAlg : IsAlgebraic (Polynomial ℚ) f) :
    ∃ N : ℕ, IsCoeffIntegralAdjointInvNat f N := by sorry

end LamLitt
