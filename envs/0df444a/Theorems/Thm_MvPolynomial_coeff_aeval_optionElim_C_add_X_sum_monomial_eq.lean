-- Prove2me | Theorems.Thm_MvPolynomial_coeff_aeval_optionElim_C_add_X_sum_monomial_eq
-- name    : MvPolynomial.coeff_aeval_optionElim_C_add_X_sum_monomial_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/6d7c4f5d-3349-592c-a910-07de5ce41201
-- title:
--   Low coefficients agree under polynomial and power-series substitution
-- statement:
--   Let $K$ be a commutative ring and let $e, m$ be natural numbers. Let $H$ be a polynomial in $K$-coefficients over the variable set $\mathrm{Option}(\mathrm{Fin}\ e)$, that is, in one distinguished variable indexed by `none` together with variables indexed by $j \in \mathrm{Fin}\ e$. Let $a \in K$, let $w : \mathrm{Fin}\ e \to \mathrm{Fin}\ m \to K$ be a family of scalars, and let $Y_j \in K[[X]]$ for $j \in \mathrm{Fin}\ e$ be power series such that for every $j$ and every $i \in \mathrm{Fin}\ m$ the coefficient of $X^{i}$ in $Y_j$ equals $w_{j,i}$. Then for every $i \in \mathrm{Fin}\ m$ the coefficient of $X^{i}$ in the polynomial obtained from $H$ by the $K$-algebra evaluation sending the distinguished variable to $C(a) + X \in K[X]$ and the variable $j$ to the truncated jet $\sum_{r \in \mathrm{Fin}\ m} w_{j,r} X^{r} \in K[X]$ coincides with the coefficient of $X^{i}$ in the power series obtained from $H$ by the $K$-algebra evaluation sending the distinguished variable to $C(a) + X \in K[[X]]$ and the variable $j$ to $Y_j$. The left-hand side is a coefficient of a polynomial, the right-hand side a coefficient of a power series.
--
--   This is the comparison between a multivariate polynomial expression evaluated at finite jets and the same expression evaluated at genuine power series: agreement modulo $X^m$ of the substituted arguments forces agreement of all coefficients in degrees below $m$. It serves as the bridge between incidence systems whose unknowns are the finitely many jet coefficients $w_{j,r}$ and statements about Taylor expansions at a rational place, and is used in the analysis of prolongation tuples and of the Jacobian at the centre in the place-specialisation theory for modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_coeff_aeval_optionElim_C_add_X_sum_monomial_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem MvPolynomial.coeff_aeval_optionElim_C_add_X_sum_monomial_eq {K : Type*} [CommRing K] {e m : ℕ}
    (H : MvPolynomial (Option (Fin e)) K) (a : K) (w : Fin e → Fin m → K) (Y : Fin e → PowerSeries K)
    (hY : ∀ j (i : Fin m), PowerSeries.coeff (i : ℕ) (Y j) = w j i) (i : Fin m) :
    (MvPolynomial.aeval (fun o : Option (Fin e) =>
        Option.elim o (Polynomial.C a + Polynomial.X)
          (fun j => ∑ r : Fin m, Polynomial.monomial (r : ℕ) (w j r))) H).coeff i
      = PowerSeries.coeff (i : ℕ) (MvPolynomial.aeval (fun o : Option (Fin e) =>
        Option.elim o (PowerSeries.C a + PowerSeries.X) Y) H) := by sorry
