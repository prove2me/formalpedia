-- Prove2me | Theorems.Thm_ModularCurve_eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero
-- name    : ModularCurve.eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/c5b44159-1ccf-524f-9003-e37c64ad9b12
-- title:
--   Injectivity of P ↦ P(j(q)) on low-order coefficients
-- statement:
--   Let $P \in \mathbb{Z}[X]$ and let $n$ be a natural number with $\deg P \le n$ (in the Lean sense, `P.natDegree ≤ n`, so the zero polynomial is allowed). Write `evalAtJ` for the ring homomorphism $\mathbb{Z}[X] \to \mathbb{Q}((q))$ into Laurent series over $\mathbb{Q}$ — that is, Hahn series with value group $\mathbb{Z}$ — obtained by evaluating a polynomial at the element `jq`, the formal $q$-expansion of the modular invariant $j$; its coefficients are thus indexed by integers. Assume that for every integer $m$ with $-n \le m \le 0$ the $m$-th coefficient of $P(j(q))$ vanishes, i.e. the Laurent series $P(j(q))$ has no term $q^m$ in the range from $q^{-n}$ through $q^{0}$. The conclusion is that $P = 0$. Equivalently, a polynomial of degree at most $n$ with integer coefficients is determined by the $n+1$ coefficients of its $q$-expansion in degrees $-n, \dots, 0$, the map in question being injective on that range of degrees.
--
--   This is the elementary finite-check principle underlying the identification of a modular function, holomorphic on the upper half-plane and meromorphic at the cusp, as a polynomial in $j$ by finitely many Fourier coefficients, here stated purely formally for the $q$-expansion of $j$. It is used in the verification of the explicit modular polynomials attached to the data for levels $2$ and $3$, being cited by [`ModularCurve.ModularPolynomialData.phi_eq_phiTwo`](thm.html#ModularCurve.ModularPolynomialData.phi_eq_phiTwo) and [`ModularCurve.ModularPolynomialData.phi_eq_phiThree`](thm.html#ModularCurve.ModularPolynomialData.phi_eq_phiThree).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_X0

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open ModularCurve Polynomial

theorem ModularCurve.eq_zero_of_natDegree_le_of_coeff_evalAtJ_eq_zero (P : Polynomial ℤ) (n : ℕ)
    (hP : P.natDegree ≤ n) (h : ∀ m : ℤ, -(n : ℤ) ≤ m → m ≤ 0 → (evalAtJ P).coeff m = 0) : P = 0 := by sorry
