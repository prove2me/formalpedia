-- Prove2me | Theorems.Thm_LamLitt_isSolutionOfAlgebraicODE_smul_rescale
-- name    : LamLitt.isSolutionOfAlgebraicODE_smul_rescale
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-21T23:14:33.203615+00:00
-- url     : https://prove2.me/theorems/d375cedf-1734-464a-8688-5909f4fac89e
-- title:
--   Non-singular algebraic ODEs are stable under $f(z)\mapsto a\,f(bz)$
-- statement:
--   Let $n\ge 0$, let $g\in\mathbb{Q}(z,y_0,\dots,y_{n-1})$ be a rational function in $n+1$ variables, and let $f=\sum_{k\ge 0}a_kz^k\in\mathbb{Q}[[z]]$ be a formal power series that solves the algebraic differential equation
--
--   $$f^{(n)}(z)=g\bigl(z,f(z),f'(z),\dots,f^{(n-1)}(z)\bigr)$$
--
--   at a non-singular point, meaning that $g$ is defined at $\bigl(0,f(0),f'(0),\dots,f^{(n-1)}(0)\bigr)$.
--
--   Let $a,b\in\mathbb{Q}$ be non-zero. Then the power series
--
--   $$F(z)=a\,f(bz)=\sum_{k\ge 0}a\,b^k a_k z^k$$
--
--   again solves an algebraic differential equation of the same order $n$ at a non-singular point: there is a rational function $\tilde g\in\mathbb{Q}(z,y_0,\dots,y_{n-1})$, defined at $\bigl(0,F(0),\dots,F^{(n-1)}(0)\bigr)$, such that $F^{(n)}(z)=\tilde g\bigl(z,F(z),\dots,F^{(n-1)}(z)\bigr)$. One may take
--
--   $$\tilde g(z,y_0,\dots,y_{n-1})=a\,b^{n}\,g\Bigl(bz,\frac{y_0}{a},\frac{y_1}{ab},\dots,\frac{y_{n-1}}{ab^{\,n-1}}\Bigr).$$
--
--   The class of power series to which the Lam–Litt conjecture applies is therefore invariant under the changes of variable $z\mapsto bz$ and under multiplication by non-zero constants. Together with a geometric bound on denominators this is used to replace a solution with coefficients in $\mathbb{Z}[1/N]$ by a solution with integer coefficients.
--
--   **Formalization Note** The hypothesis on $f$ and $g$ is the mission's predicate `IsSolutionOfAlgebraicODE`: $g=p/q$ for polynomials $p,q$ with $q\bigl(0,f(0),\dots,f^{(n-1)}(0)\bigr)\neq 0$ and $f^{(n)}\cdot q(z,f,\dots,f^{(n-1)})=p(z,f,\dots,f^{(n-1)})$ in $\mathbb{Q}[[z]]$. The order $n=0$ is allowed; then $f$ is a rational function without pole at $0$. The series $F$ is written `a • PowerSeries.rescale b f`. The conclusion only asserts the existence of some $\tilde g$ for which $F$ satisfies `IsSolutionOfAlgebraicODE`.
-- source:
--   Change of variables in the setting of Conjecture 1.1.1 of Y. H. J. Lam, D. Litt, Algebraicity and integrality of solutions to differential equations, https://arxiv.org/abs/2501.13175 (v1), pp. 2-3 (equation (1.1) and footnote 1). Elementary; not stated in the paper. Introduced as a step in the reduction of implication (2) => (1) of the conjecture (D. Litt, Problem 1, https://www.problemsilike.com/1 ) to power series with integer coefficients.

import Definitions.Def_LamLitt_Defs
import Mathlib

open PowerSeries

namespace LamLitt

theorem isSolutionOfAlgebraicODE_smul_rescale {n : ℕ} (f : PowerSeries ℚ)
    (g : MvRatFunc (Fin (n + 1)) ℚ) (hODE : IsSolutionOfAlgebraicODE n f g)
    (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    ∃ g' : MvRatFunc (Fin (n + 1)) ℚ,
      IsSolutionOfAlgebraicODE n (a • PowerSeries.rescale b f) g' := by sorry

end LamLitt
