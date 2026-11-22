-- Prove2me | Theorems.Thm_LamLitt_integer_coefficients_implies_algebraicity
-- name    : LamLitt.integer_coefficients_implies_algebraicity
-- status  : Open
-- author  : @emmgaml
-- created : 2026-11-21T23:14:30.933027+00:00
-- url     : https://prove2.me/theorems/87f5fcf2-2f78-4746-a6a0-7db88735400d
-- title:
--   Lam–Litt conjecture, integral form: solutions in $\mathbb{Z}[[z]]$ are algebraic
-- statement:
--   Let $n\ge 0$, let $g\in\mathbb{Q}(z,y_0,\dots,y_{n-1})$ be a rational function in $n+1$ variables, and let $f=\sum_{k\ge 0}a_kz^k\in\mathbb{Q}[[z]]$ be a formal power series that solves the algebraic differential equation
--
--   $$f^{(n)}(z)=g\bigl(z,f(z),f'(z),\dots,f^{(n-1)}(z)\bigr)$$
--
--   at a non-singular point, meaning that $g$ is defined at $\bigl(0,f(0),f'(0),\dots,f^{(n-1)}(0)\bigr)$.
--
--   If all coefficients of $f$ are integers, that is $f\in\mathbb{Z}[[z]]$, then $f$ is algebraic over $\mathbb{Q}[z]$:
--
--   $$a_k\in\mathbb{Z}\ \text{ for all }k\ge 0\quad\Longrightarrow\quad f\text{ is algebraic over }\mathbb{Q}[z].$$
--
--   This is an open problem: it is the case $N=1$ of implication (2)$\Rightarrow$(1) of the Lam–Litt conjecture, which asks the same conclusion when $a_k\in\mathbb{Z}[1/N]$ for some $N$ (Problem 1 on Litt's list). The two statements are equivalent. A solution with coefficients in $\mathbb{Z}[1/N]$ satisfies $M^{k+1}a_k\in\mathbb{Z}$ for a suitable integer $M\ge 1$, the rescaled series $M f(Mz)$ has integer coefficients and again solves a non-singular algebraic differential equation of order $n$, and $f$ is algebraic if and only if $M f(Mz)$ is. The integral form removes the auxiliary integer $N$ from the problem.
--
--   **Formalization Note** The hypothesis on $f$ and $g$ is the mission's predicate `IsSolutionOfAlgebraicODE`: $g=p/q$ for polynomials $p,q$ with $q\bigl(0,f(0),\dots,f^{(n-1)}(0)\bigr)\neq 0$ and $f^{(n)}\cdot q(z,f,\dots,f^{(n-1)})=p(z,f,\dots,f^{(n-1)})$ in $\mathbb{Q}[[z]]$. The order $n=0$ is allowed; then $f$ is a rational function without pole at $0$. Integrality is stated as: every coefficient of $f$ is the image of an integer. Algebraicity is `IsAlgebraic (Polynomial ℚ) f`, for the action of $\mathbb{Q}[z]$ on $\mathbb{Q}[[z]]$.
-- source:
--   Special case N = 1 of implication (2) => (1) of Conjecture 1.1.1 of Y. H. J. Lam, D. Litt, Algebraicity and integrality of solutions to differential equations, https://arxiv.org/abs/2501.13175 (v1), p. 3; the implication (2) => (1) is Problem 1 of D. Litt, https://www.problemsilike.com/1 , and is formalized in Formal Conjectures, FormalConjectures/LittProblems/1.lean (lam_litt.variants.integrality_implies_algebraicity), https://github.com/google-deepmind/formal-conjectures . The integer-coefficient normalization is not stated in these sources; it is equivalent to the general case by the rescaling z -> Mz.

import Definitions.Def_LamLitt_Defs
import Mathlib

open PowerSeries

namespace LamLitt

theorem integer_coefficients_implies_algebraicity {n : ℕ} (f : PowerSeries ℚ)
    (g : MvRatFunc (Fin (n + 1)) ℚ) (hODE : IsSolutionOfAlgebraicODE n f g)
    (hZ : ∀ k : ℕ, ∃ m : ℤ, PowerSeries.coeff k f = (m : ℚ)) :
    IsAlgebraic (Polynomial ℚ) f := by sorry

end LamLitt
