-- Prove2me | Theorems.Thm_LamLitt_omega_integrality_implies_integrality
-- name    : LamLitt.omega_integrality_implies_integrality
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T16:41:36.557517+00:00
-- url     : https://prove2.me/theorems/edd4eb4f-3e1b-47ce-812b-33d78afbe936
-- title:
--   Lam–Litt: $\omega$-integrality implies bounded denominators
-- statement:
--   Let $n\ge0$, $g\in\mathbb{Q}(z,y_0,\dots,y_{n-1})$ and let $f=\sum_k a_kz^k\in\mathbb{Q}[[z]]$ satisfy $f^{(n)}=g(z,f,\dots,f^{(n-1)})$ with $g(0,f(0),\dots,f^{(n-1)}(0))$ defined. Suppose there is an integer-valued function $\omega$ on the primes with $\lim_{p\to\infty}\omega(p)/p=\infty$ such that for each prime $p$ the numbers $a_0,\dots,a_{\omega(p)}$ lie in $\mathbb{Z}_{(p)}$. Then there is $N$ with
--   $$a_k\in\mathbb{Z}[1/N]\qquad\text{for all }k\ge0.$$
--
--   This is the implication (3)⇒(2) of the Lam–Litt conjecture. It is open; it follows from the full conjecture via Eisenstein's theorem.
--
--   **Formalization Note** The ODE hypothesis is `IsSolutionOfAlgebraicODE`, as in the goal theorem.
-- source:
--   Formal Conjectures, FormalConjectures/LittProblems/1.lean (Lam--Litt conjecture); Y. H. J. Lam, D. Litt, Algebraicity and integrality of solutions to differential equations, https://arxiv.org/abs/2501.13175; D. Litt, Problem 1, https://www.problemsilike.com/1

import Definitions.Def_LamLitt_Defs
import Mathlib

open PowerSeries

namespace LamLitt

theorem omega_integrality_implies_integrality {n : ℕ} (f : PowerSeries ℚ)
    (g : MvRatFunc (Fin (n + 1)) ℚ) (hODE : IsSolutionOfAlgebraicODE n f g)
    (ω : Nat.Primes → ℤ) (hω : omegaSuperlinear ω ∧ omegaIntegral ω (PowerSeries.coeff · f)) :
    ∃ N : ℕ, IsCoeffIntegralAdjointInvNat f N := by sorry

end LamLitt
