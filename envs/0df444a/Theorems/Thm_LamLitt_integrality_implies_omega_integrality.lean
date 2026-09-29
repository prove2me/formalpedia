-- Prove2me | Theorems.Thm_LamLitt_integrality_implies_omega_integrality
-- name    : LamLitt.integrality_implies_omega_integrality
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T16:36:57.282428+00:00
-- url     : https://prove2.me/theorems/1cf43be1-2188-4d08-9cdd-f24b2ecbbb7a
-- title:
--   Bounded denominators imply $\omega$-integrality
-- statement:
--   Let $f=\sum_{k\ge0}a_kz^k\in\mathbb{Q}[[z]]$ and $N\in\mathbb{N}$ with $a_k\in\mathbb{Z}[1/N]$ for all $k$. Then there is an integer-valued function $\omega$ on the primes with
--   $$\lim_{p\to\infty}\frac{\omega(p)}{p}=\infty$$
--   such that, for every prime $p$, the rational numbers $a_0,a_1,\dots,a_{\omega(p)}$ lie in $\mathbb{Z}_{(p)}$.
--
--   This is the elementary implication (2)⇒(3) of the Lam–Litt conjecture; it holds without any differential equation hypothesis.
--
--   **Formalization Note** $\omega$ may take negative values, in which case the condition at that prime is empty.
-- source:
--   Formal Conjectures, FormalConjectures/LittProblems/1.lean (Lam--Litt conjecture); Y. H. J. Lam, D. Litt, Algebraicity and integrality of solutions to differential equations, https://arxiv.org/abs/2501.13175; D. Litt, Problem 1, https://www.problemsilike.com/1

import Definitions.Def_LamLitt_Defs
import Mathlib

open PowerSeries

namespace LamLitt

theorem integrality_implies_omega_integrality
    (f : PowerSeries ℚ) (N : ℕ) (hN : IsCoeffIntegralAdjointInvNat f N) :
    ∃ ω : Nat.Primes → ℤ, omegaSuperlinear ω ∧ omegaIntegral ω (PowerSeries.coeff · f) := by sorry

end LamLitt
