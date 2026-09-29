-- Prove2me | Theorems.Thm_LamLitt_lam_litt_conjecture
-- name    : LamLitt.lam_litt_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-27T16:42:52.981807+00:00
-- url     : https://prove2.me/theorems/7f942e51-c7f7-4b1a-a63e-e4b8cb92c23e
-- title:
--   Lam–Litt conjecture
-- statement:
--   Let $n\ge 0$, let $g\in\mathbb{Q}(z,y_0,\dots,y_{n-1})$ be a rational function in $n+1$ variables, and let $f=\sum_{k\ge0}a_kz^k\in\mathbb{Q}[[z]]$ satisfy
--   $$f^{(n)}(z)=g\bigl(z,f(z),f'(z),\dots,f^{(n-1)}(z)\bigr),$$
--   where $g\bigl(0,f(0),f'(0),\dots,f^{(n-1)}(0)\bigr)$ is defined. Then the following are equivalent:
--
--   1. $f$ is algebraic over $\mathbb{Q}[z]$;
--   2. there exists $N$ such that $a_k\in\mathbb{Z}[1/N]$ for all $k$;
--   3. there exists an integer-valued function $\omega$ on the primes with $\lim_{p\to\infty}\omega(p)/p=\infty$ such that, for each prime $p$, the rational numbers $a_0,a_1,\dots,a_{\omega(p)}$ lie in $\mathbb{Z}_{(p)}$.
--
--   The implication (1)⇒(2) is Eisenstein's theorem and (2)⇒(3) is elementary; the conjecture is the content of (3)⇒(1). For linear equations it strengthens the Grothendieck–Katz $p$-curvature conjecture.
--
--   **Formalization Note** The ODE hypothesis is the definition `IsSolutionOfAlgebraicODE` (a representation $g=p/q$ with $q$ nonzero at the initial point and $f^{(n)}q(\dots)=p(\dots)$). Algebraicity is over the polynomial ring $\mathbb{Q}[z]$ acting on $\mathbb{Q}[[z]]$; the three conditions are stated as a `List.TFAE`.
-- source:
--   Formal Conjectures, FormalConjectures/LittProblems/1.lean (Lam--Litt conjecture); Y. H. J. Lam, D. Litt, Algebraicity and integrality of solutions to differential equations, https://arxiv.org/abs/2501.13175; D. Litt, Problem 1, https://www.problemsilike.com/1

import Definitions.Def_LamLitt_Defs
import Mathlib

open PowerSeries

namespace LamLitt

theorem lam_litt_conjecture {n : ℕ} (f : PowerSeries ℚ) (g : MvRatFunc (Fin (n + 1)) ℚ)
    (hODE : IsSolutionOfAlgebraicODE n f g) :
    List.TFAE
      [IsAlgebraic (Polynomial ℚ) f,
       ∃ N : ℕ, IsCoeffIntegralAdjointInvNat f N,
       ∃ ω : Nat.Primes → ℤ, omegaSuperlinear ω ∧ omegaIntegral ω (PowerSeries.coeff · f)] := by sorry

end LamLitt
