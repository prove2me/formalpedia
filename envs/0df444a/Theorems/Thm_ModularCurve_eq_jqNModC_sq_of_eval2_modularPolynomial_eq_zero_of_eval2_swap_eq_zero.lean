-- Prove2me | Theorems.Thm_ModularCurve_eq_jqNModC_sq_of_eval2_modularPolynomial_eq_zero_of_eval2_swap_eq_zero
-- name    : ModularCurve.eq_jqNModC_sq_of_eval2_modularPolynomial_eq_zero_of_eval2_swap_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/0fc81f8b-92ef-5f26-bc36-6503c2101bab
-- title:
--   Uniqueness of the common root jmath̃(q^{ℓ^2}) of two modular equations
-- statement:
--   Let $\kappa$ be a field, let $N \ge 1$ be a natural number and $\ell$ a prime, and assume that the images of $N$ and of $\ell$ in $\kappa$ are nonzero. Write $\tilde\jmath = \mathrm{jqModC}\,\kappa$ for the Laurent series $q^{-1}$ times the image in $\kappa$ of the integral power series $\mathrm{jNum}$, so that for $m \ge 1$ the series $\mathrm{jqNModC}\,\kappa\,m$ is obtained from $\tilde\jmath$ by multiplying all exponents by $m$, i.e. it is $\tilde\jmath(q^m)$. Let `dataN` and `dataℓ` be modular polynomial data of levels $N$ and $\ell$: each consists of a polynomial $\Phi \in \mathbb{Z}[X][Y]$ that is monic in $Y$, whose degree in $Y$ equals $\sum_{d \mid N,\ d \text{ squarefree}} N/d$ (respectively the same sum for $\ell$), and which satisfies $\Phi(j(q), j(q^N)) = 0$ (respectively $\Phi(j(q), j(q^{\ell})) = 0$) for the rational $q$-expansions. Let $y \in \kappa((q))$ satisfy the two modular equations $\Phi_{\ell}\bigl(\tilde\jmath(q^{\ell}), y\bigr) = 0$ and $\Phi_N\bigl(y, \tilde\jmath(q^{N\ell^2})\bigr) = 0$, where in each case the coefficients in $\mathbb{Z}[X]$ are evaluated at the indicated series and the outer variable at the other one. Then $y = \tilde\jmath(q^{\ell^2})$. Thus only the uniqueness half of the classical statement is asserted; existence of such a $y$ is not part of the conclusion.
--
--   This is the computational crux behind the Fricke-type involution on the $\ell$-roof of the modular tower: the $q$-expansion $\tilde\jmath(q^{\ell^2})$ is pinned down as the unique series that is simultaneously $\ell$-isogenous to $\tilde\jmath(q^{\ell})$ and $N$-co-isogenous to $\tilde\jmath(q^{N\ell^2})$. It is used in the construction of the swap isomorphism and the degeneracy maps in [`ModularCurve.exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap`](thm.html#ModularCurve.exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_jqNModC_sq_of_eval2_modularPolynomial_eq_zero_of_eval2_swap_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.eq_jqNModC_sq_of_eval2_modularPolynomial_eq_zero_of_eval2_swap_eq_zero
    (κ : Type*) [Field κ] (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime]
    (hN : (N : κ) ≠ 0) (hℓ : (ℓ : κ) ≠ 0)
    (dataN : ModularCurve.ModularPolynomialData N) (dataℓ : ModularCurve.ModularPolynomialData ℓ)
    (y : LaurentSeries κ)
    (h₁ : dataℓ.Φ.eval₂ (Polynomial.aeval (R := ℤ) (ModularCurve.jqNModC κ ℓ)).toRingHom y = 0)
    (h₂ : dataN.Φ.eval₂ (Polynomial.aeval (R := ℤ) y).toRingHom (ModularCurve.jqNModC κ (N * ℓ * ℓ)) = 0) :
    y = ModularCurve.jqNModC κ (ℓ * ℓ) := by sorry
