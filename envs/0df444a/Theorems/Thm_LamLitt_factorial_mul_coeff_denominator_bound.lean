-- Prove2me | Theorems.Thm_LamLitt_factorial_mul_coeff_denominator_bound
-- name    : LamLitt.factorial_mul_coeff_denominator_bound
-- status  : Proved
-- author  : @emmgaml
-- created : 2026-11-21T23:14:34.144254+00:00
-- url     : https://prove2.me/theorems/f83a9588-b1ab-47f3-8862-d60f3957f251
-- title:
--   Solutions of non-singular algebraic ODEs: $D^{k+1}\,k!\,a_k\in\mathbb{Z}$
-- statement:
--   Let $n\ge 0$, let $g\in\mathbb{Q}(z,y_0,\dots,y_{n-1})$ be a rational function in $n+1$ variables, and let $f=\sum_{k\ge 0}a_kz^k\in\mathbb{Q}[[z]]$ be a formal power series that solves the algebraic differential equation
--
--   $$f^{(n)}(z)=g\bigl(z,f(z),f'(z),\dots,f^{(n-1)}(z)\bigr)$$
--
--   at a non-singular point, meaning that $g$ is defined at $\bigl(0,f(0),f'(0),\dots,f^{(n-1)}(0)\bigr)$.
--
--   Then there is an integer $D\ge 1$ such that
--
--   $$D^{k+1}\,k!\,a_k\in\mathbb{Z}\qquad\text{for all }k\ge 0.$$
--
--   Since $k!\,a_k=f^{(k)}(0)$, the statement says that the denominators of the derivatives of $f$ at the origin grow at most geometrically: $D^{k+1}f^{(k)}(0)\in\mathbb{Z}$ for all $k$.
--
--   This is the basic arithmetic property of power series solutions of algebraic differential equations at a non-singular point. It shows that the only source of unbounded denominators in $a_k$ is the factorial $k!$: for every prime $p\nmid D$ one gets $v_p(a_k)\ge -v_p(k!)$, so $a_0,\dots,a_{p-1}$ are automatically $p$-integral, and $f$ has a positive $p$-adic radius of convergence at every prime $p$. Combined with a bounded-denominator hypothesis it yields a geometric bound on the denominators of the $a_k$ themselves (`LamLitt.coeff_denominator_bound_of_integrality`), which is what allows one to rescale a solution with coefficients in $\mathbb{Z}[1/N]$ to one with integer coefficients.
--
--   **Formalization Note** The hypothesis on $f$ and $g$ is the mission's predicate `IsSolutionOfAlgebraicODE`: $g=p/q$ for polynomials $p,q$ with $q\bigl(0,f(0),\dots,f^{(n-1)}(0)\bigr)\neq 0$ and $f^{(n)}\cdot q(z,f,\dots,f^{(n-1)})=p(z,f,\dots,f^{(n-1)})$ in $\mathbb{Q}[[z]]$. The order $n=0$ is allowed; then $f$ is a rational function without pole at $0$. The conclusion is stated as: there is a natural number $D>0$ such that for every $k$ the rational number $D^{k+1}\cdot(k!\cdot a_k)$ is the image of an integer.
-- source:
--   Auxiliary lemma for Conjecture 1.1.1 of Y. H. J. Lam, D. Litt, Algebraicity and integrality of solutions to differential equations, https://arxiv.org/abs/2501.13175 (v1), p. 3 (setting of equation (1.1) and footnote 1 for the non-singularity hypothesis). The statement itself is not in that paper: it is the elementary non-singular case of the p-adic growth bounds for differentially algebraic power series, cf. Y. Sibuya, S. Sperber, Arithmetic properties of power series solutions of algebraic differential equations, Ann. of Math. (2) 113 (1981), 111-157, p. 112, Eq. (III') (as recalled on p. 2 of the next reference), and C. Krattenthaler, T. Rivoal, Arithmetic properties of the Taylor coefficients of differentially algebraic power series, https://arxiv.org/abs/2502.09259 (v1), Theorem 1 and Corollary 1, p. 5.

import Definitions.Def_LamLitt_Defs
import Mathlib

open PowerSeries

namespace LamLitt

theorem factorial_mul_coeff_denominator_bound {n : ℕ} (f : PowerSeries ℚ)
    (g : MvRatFunc (Fin (n + 1)) ℚ) (hODE : IsSolutionOfAlgebraicODE n f g) :
    ∃ D : ℕ, 0 < D ∧ ∀ k : ℕ, ∃ m : ℤ,
      (D : ℚ) ^ (k + 1) * ((k.factorial : ℚ) * PowerSeries.coeff k f) = (m : ℚ) := by sorry

end LamLitt
