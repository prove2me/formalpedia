-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_isHomogeneous_sub_two_and_sum_pderiv_pderiv_eq_zero_lowerTwo_xi
-- name    : LanglandsTunnell.CubicInduction.isHomogeneous_sub_two_and_sum_pderiv_pderiv_eq_zero_lowerTwo_xi
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:07.012626+00:00
-- url     : https://prove2.me/theorems/1047e4ad-b399-5d40-b7c5-b402e226da8b
-- title:
--   Harmonicity and degree ℓ-2 of lower₂(Xi_ν p)
-- statement:
--   Let $\nu \in \mathbb{C}^3$ (a function $\mathrm{Fin}\,3 \to \mathbb{C}$), let $\ell$ be a natural number, and let $p \in \mathbb{C}[x_0,x_1,x_2]$ be a polynomial in three variables which is homogeneous of degree $\ell$ and satisfies $\sum_{i} \partial_i \partial_i p = 0$. Introduce the $3\times 3$ matrix $\Xi(\nu,p)$ with entries in $\mathbb{C}[x_0,x_1,x_2]$ given by $\Xi(\nu,p)_{cc} = 2(\nu_c + \rho_c)\,p$ with $\rho = (1,0,-1)$, and, for $c \neq d$, $\Xi(\nu,p)_{cd} = -\bigl(x_{\max(c,d)}\,\partial_{\min(c,d)} p - x_{\min(c,d)}\,\partial_{\max(c,d)} p\bigr)$; and let $\mathrm{lower}_2(M) = \sum_{c}\sum_{d} \partial_c \partial_d (M_{cd})$ for a $3\times 3$ matrix $M$ of such polynomials. The conclusion is twofold: $\mathrm{lower}_2(\Xi(\nu,p))$ is homogeneous of degree $\ell - 2$, the subtraction being truncated subtraction of natural numbers (so for $\ell \le 2$ the asserted degree is $0$), and $\sum_i \partial_i \partial_i \bigl(\mathrm{lower}_2(\Xi(\nu,p))\bigr) = 0$, i.e. the result is again harmonic. Here $\partial_i$ denotes `MvPolynomial.pderiv i`, and $\Xi$ and $\mathrm{lower}_2$ are introduced as local abbreviations inside the statement.
--
--   A statement about harmonic homogeneous polynomials in three variables: the entries of $\Xi_\nu p$ are obtained from $p$ by scalars and by the infinitesimal rotations $x_d\partial_c - x_c\partial_d$, all of which commute with the Laplacian, as do the second derivatives $\partial_c\partial_d$. It supplies the degree and harmonicity bookkeeping for the construction of transition-stable families of $K$-types in the compact picture of a principal series of $GL_3(\mathbb{R})$, and is used by [`LanglandsTunnell.CubicInduction.exists_transitionStable_family_of_signIsotypic_submodule`](thm.html#LanglandsTunnell.CubicInduction.exists_transitionStable_family_of_signIsotypic_submodule) and [`LanglandsTunnell.CubicInduction.exists_transitionStable_family_read_of_actStable_signIsotypic`](thm.html#LanglandsTunnell.CubicInduction.exists_transitionStable_family_read_of_actStable_signIsotypic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_isHomogeneous_sub_two_and_sum_pderiv_pderiv_eq_zero_lowerTwo_xi.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem LanglandsTunnell.CubicInduction.isHomogeneous_sub_two_and_sum_pderiv_pderiv_eq_zero_lowerTwo_xi
    (ν : Fin 3 → ℂ) (ℓ : ℕ) (p : MvPolynomial (Fin 3) ℂ) (hp : p.IsHomogeneous ℓ)
    (hharm : (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i p)) = 0) :
    let Ξ : (Fin 3 → ℂ) → MvPolynomial (Fin 3) ℂ → Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) :=
      fun ν p => Matrix.of fun c d =>
        if c = d then MvPolynomial.C (2 * (ν c + (![1, 0, -1] : Fin 3 → ℂ) c)) * p
        else -(MvPolynomial.X (max c d) * MvPolynomial.pderiv (min c d) p -
          MvPolynomial.X (min c d) * MvPolynomial.pderiv (max c d) p)
    let lower₂ : Matrix (Fin 3) (Fin 3) (MvPolynomial (Fin 3) ℂ) → MvPolynomial (Fin 3) ℂ :=
      fun M => ∑ c : Fin 3, ∑ d : Fin 3, MvPolynomial.pderiv c (MvPolynomial.pderiv d (M c d))
    (lower₂ (Ξ ν p)).IsHomogeneous (ℓ - 2) ∧
      (∑ i : Fin 3, MvPolynomial.pderiv i (MvPolynomial.pderiv i (lower₂ (Ξ ν p)))) = 0 := by sorry
