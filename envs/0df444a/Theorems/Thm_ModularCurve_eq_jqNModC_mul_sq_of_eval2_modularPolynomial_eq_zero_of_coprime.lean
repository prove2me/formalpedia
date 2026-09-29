-- Prove2me | Theorems.Thm_ModularCurve_eq_jqNModC_mul_sq_of_eval2_modularPolynomial_eq_zero_of_coprime
-- name    : ModularCurve.eq_jqNModC_mul_sq_of_eval2_modularPolynomial_eq_zero_of_coprime
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/750e83a1-f6c1-5bc5-bdeb-f80d3191eb25
-- title:
--   Uniqueness of the common root of Φ_ℓ and Φ_N
-- statement:
--   Let $\kappa$ be a field, let $N \ge 1$ be a natural number and $\ell$ a prime with $\ell \nmid N$, and assume that both $N$ and $\ell$ are nonzero in $\kappa$. Write $\tilde j \in \kappa((q))$ for [`ModularCurve.jqModC`](def/ModularCurve_JqCoeff.html#L15), the reduction to $\kappa$ of the $q$-expansion $q^{-1}\cdot(\text{integral power series})$ of the modular invariant, and for $M \ge 1$ write $\tilde j_M =$ [`ModularCurve.jqNModC`](def/ModularCurve_JqCoeff.html#L18) $\kappa\,M$ for its image under the exponent-scaling ring homomorphism $q \mapsto q^{M}$. Let `dataN` and `dataℓ` be modular polynomial data of levels $N$ and $\ell$: each consists of a polynomial $\Phi \in \mathbb{Z}[X][Y]$ that is monic in $Y$, of degree in $Y$ equal to $\sum_{d \mid M,\ d \text{ squarefree}} M/d$, and satisfies $\Phi(j(q), j(q^{M})) = 0$ in $\mathbb{Q}((q))$. Let $y \in \kappa((q))$ be a Laurent series such that $\Phi_\ell(\tilde j_{N^2\ell},\, y) = 0$ and $\Phi_N(\tilde j_{N\ell^2},\, y) = 0$, where in each case the coefficients in $\mathbb{Z}[X]$ are evaluated at the indicated Laurent series and the outer variable at $y$. Then $y = \tilde j_{N^2\ell^2}$. Thus only uniqueness of such a common root is asserted, not its existence.
--
--   This is the uniqueness half of the classical statement that the only $q$-series simultaneously $\ell$-isogenous to $\tilde j_{N^2\ell}$ and $N$-isogenous to $\tilde j_{N\ell^2}$ is $\tilde j_{N^2\ell^2}$, i.e. the rigidity underlying the Atkin–Lehner involution $W_\ell$ on the level-$N\ell$ tower. It is used in the construction of the automorphism swapping the two degeneracy maps of the $\ell$-roof, in [`ModularCurve.exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap`](thm.html#ModularCurve.exists_algEquiv_modularFunctionFieldC_swap_and_charLDegeneracyRoof_swap).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_jqNModC_mul_sq_of_eval2_modularPolynomial_eq_zero_of_coprime.lean

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_JqCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ModularCurve.eq_jqNModC_mul_sq_of_eval2_modularPolynomial_eq_zero_of_coprime
    (κ : Type*) [Field κ] (N : ℕ) [NeZero N] (ℓ : ℕ) [Fact ℓ.Prime] (hℓN : ¬ ℓ ∣ N)
    (hN : (N : κ) ≠ 0) (hℓ : (ℓ : κ) ≠ 0)
    (dataN : ModularCurve.ModularPolynomialData N) (dataℓ : ModularCurve.ModularPolynomialData ℓ)
    (y : LaurentSeries κ)
    (h₁ : dataℓ.Φ.eval₂ (Polynomial.aeval (R := ℤ) (ModularCurve.jqNModC κ (N * N * ℓ))).toRingHom y = 0)
    (h₂ : dataN.Φ.eval₂ (Polynomial.aeval (R := ℤ) (ModularCurve.jqNModC κ (N * ℓ * ℓ))).toRingHom y = 0) :
    y = ModularCurve.jqNModC κ (N * N * ℓ * ℓ) := by sorry
