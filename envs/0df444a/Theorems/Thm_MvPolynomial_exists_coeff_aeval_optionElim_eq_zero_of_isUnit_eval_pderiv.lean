-- Prove2me | Theorems.Thm_MvPolynomial_exists_coeff_aeval_optionElim_eq_zero_of_isUnit_eval_pderiv
-- name    : MvPolynomial.exists_coeff_aeval_optionElim_eq_zero_of_isUnit_eval_pderiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/4a4f97b2-c97b-58a0-9a24-5e886ede521b
-- title:
--   Truncated implicit functions for a triangular pair of relations
-- statement:
--   Let $A$ be a commutative ring, let $m$ be a natural number, let $u \in A$, let $w_0 : \mathrm{Fin}\,2 \to A$, and let $G_0, G_1$ be polynomials over $A$ in the variables indexed by $\mathrm{Option}(\mathrm{Fin}\,2)$, i.e. in the variables $X_{\mathrm{none}}, X_{\mathrm{some}\,0}, X_{\mathrm{some}\,1}$. Assume that $X_{\mathrm{some}\,1}$ does not occur among the variables of $G_0$ (so the pair is triangular), that the point sending $\mathrm{none} \mapsto u$ and $\mathrm{some}\,j \mapsto w_0(j)$ is a common zero of $G_0$ and $G_1$, and that for each $j \in \mathrm{Fin}\,2$ the value of the partial derivative $\partial G_j/\partial X_{\mathrm{some}\,j}$ at that point is a unit of $A$. The conclusion is that there are coefficients $w : \mathrm{Fin}\,2 \to \mathrm{Fin}(m+1) \to A$ with $w(j)(0) = w_0(j)$ for each $j$ such that, writing $W_j(T) = \sum_{r' \le m} w(j)(r')\,T^{r'} \in A[T]$, the substitution $X_{\mathrm{none}} \mapsto u + T$, $X_{\mathrm{some}\,j} \mapsto W_j(T)$ carries each $G_j$ to a polynomial in $T$ all of whose coefficients in degrees $r \le m$ vanish.
--
--   This is the truncated (jet-level) implicit function theorem, or Newton–Hensel iteration, for a triangular pair of plane relations with unit partial derivatives: the solution is produced only to order $m$ in the parameter $T$. It is applied, via the one-variable case [`Polynomial.exists_coeff_eval_sum_monomial_eq_zero_of_isUnit_derivative`](thm.html#Polynomial.exists_coeff_eval_sum_monomial_eq_zero_of_isUnit_derivative), in the construction of chart data for prolongation tuples of place specialisations on modular curves.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPolynomial_exists_coeff_aeval_optionElim_eq_zero_of_isUnit_eval_pderiv.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem MvPolynomial.exists_coeff_aeval_optionElim_eq_zero_of_isUnit_eval_pderiv
    {A : Type*} [CommRing A] (m : ℕ) (u : A) (w0 : Fin 2 → A) (G : Fin 2 → MvPolynomial (Option (Fin 2)) A)
    (hvars : (some 1 : Option (Fin 2)) ∉ (G 0).vars)
    (hroot : ∀ j, MvPolynomial.eval (fun o => Option.elim o u w0) (G j) = 0)
    (hder : ∀ j, IsUnit (MvPolynomial.eval (fun o => Option.elim o u w0) (MvPolynomial.pderiv (some j) (G j)))) :
    ∃ w : Fin 2 → Fin (m + 1) → A, (∀ j, w j 0 = w0 j) ∧
      ∀ (j : Fin 2) (r : Fin (m + 1)),
        (MvPolynomial.aeval (fun o : Option (Fin 2) => Option.elim o (Polynomial.C u + Polynomial.X)
            (fun j => ∑ r' : Fin (m + 1), Polynomial.monomial (r' : ℕ) (w j r'))) (G j)).coeff r = 0 := by sorry
