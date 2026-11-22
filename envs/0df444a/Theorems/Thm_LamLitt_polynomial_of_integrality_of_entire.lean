-- Prove2me | Theorems.Thm_LamLitt_polynomial_of_integrality_of_entire
-- name    : LamLitt.polynomial_of_integrality_of_entire
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-21T23:25:45.501196+00:00
-- url     : https://prove2.me/theorems/bc8ed41d-2bcf-461d-a5f8-28efca7444c1
-- title:
--   Entire solutions of non-singular algebraic ODEs with bounded denominators are polynomials
-- statement:
--   Let $n\ge 0$, let $g\in\mathbb{Q}(z,y_0,\dots,y_{n-1})$ be a rational function in $n+1$ variables, and let $f=\sum_{k\ge 0}a_kz^k\in\mathbb{Q}[[z]]$ be a formal power series that solves the algebraic differential equation
--
--   $$f^{(n)}(z)=g\bigl(z,f(z),f'(z),\dots,f^{(n-1)}(z)\bigr)$$
--
--   at a non-singular point, meaning that $g$ is defined at $\bigl(0,f(0),f'(0),\dots,f^{(n-1)}(0)\bigr)$.
--
--   Suppose that
--
--   1. $f$ has bounded denominators: there is $N$ with $a_k\in\mathbb{Z}[1/N]$ for all $k$;
--   2. $f$ is entire: for every $R>0$ the sequence $|a_k|R^k$ is bounded, that is, $f$ has infinite radius of convergence.
--
--   Then $f$ is a polynomial:
--
--   $$a_k=0\qquad\text{for all sufficiently large }k.$$
--
--   In particular $f$ is algebraic over $\mathbb{Q}[z]$, so implication (2)$\Rightarrow$(1) of the Lam–Litt conjecture holds for entire solutions. The differential equation enters only through the geometric bound $M^{k+1}a_k\in\mathbb{Z}$ on the denominators of a solution with bounded denominators; the analytic hypothesis enters only through the decay of the coefficients. The statement applies to every solution of a linear differential equation $y^{(n)}=c_{n-1}(z)y^{(n-1)}+\dots+c_0(z)y+r(z)$ with polynomial coefficients, since such solutions are entire.
--
--   **Formalization Note** The hypothesis on $f$ and $g$ is the mission's predicate `IsSolutionOfAlgebraicODE`. Entireness is stated without real numbers: for every natural number $R$ there is a rational $C$ with $|a_k|\,R^k\le C$ for all $k$. The conclusion is that $f$ is the image of a polynomial in $\mathbb{Q}[z]$ under the inclusion $\mathbb{Q}[z]\subset\mathbb{Q}[[z]]$.
-- source:
--   Special case (entire solutions) of implication (2) => (1) of Conjecture 1.1.1 of Y. H. J. Lam, D. Litt, Algebraicity and integrality of solutions to differential equations, https://arxiv.org/abs/2501.13175 (v1), p. 3, which is Problem 1 of D. Litt, https://www.problemsilike.com/1 . Not stated in the paper; it follows from the geometric bound on denominators of solutions with bounded denominators (theorem LamLitt.coeff_denominator_bound_of_integrality on this platform).

import Definitions.Def_LamLitt_Defs
import Mathlib

open PowerSeries

namespace LamLitt

theorem polynomial_of_integrality_of_entire {n : ℕ} (f : PowerSeries ℚ)
    (g : MvRatFunc (Fin (n + 1)) ℚ) (hODE : IsSolutionOfAlgebraicODE n f g)
    (N : ℕ) (hN : IsCoeffIntegralAdjointInvNat f N)
    (hentire : ∀ R : ℕ, ∃ C : ℚ, ∀ k : ℕ, |PowerSeries.coeff k f| * (R : ℚ) ^ k ≤ C) :
    ∃ P : Polynomial ℚ, f = (P : PowerSeries ℚ) := by sorry

end LamLitt
