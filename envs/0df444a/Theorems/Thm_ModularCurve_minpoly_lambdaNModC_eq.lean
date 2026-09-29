-- Prove2me | Theorems.Thm_ModularCurve_minpoly_lambdaNModC_eq
-- name    : ModularCurve.minpoly_lambdaNModC_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.624895+00:00
-- url     : https://prove2.me/theorems/6627a8df-d5cd-5cd5-965f-904a19c3deff
-- title:
--   Level-two modular polynomial as minimal polynomial of λ(q^q)
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $q$ be a prime natural number with $q \neq 2$, and let `data` be a term of `LambdaModularPolynomialData q`, i.e. a polynomial $\Psi \in \mathbb{Z}[X][Y]$ that is monic with $\deg_Y \Psi = q+1$ and satisfies $\Psi(\lambda, \lambda_q) = 0$ in $\mathbb{Q}((\mathfrak q))$, where $\lambda$ denotes the integral Laurent series `lambdaInt` — the product of $\mathfrak q$ with the eighth power of the eta-product series, the sixteenth power of that series with $\mathfrak q$ replaced by $\mathfrak q^4$, and the inverted eta-unit series with $\mathfrak q$ replaced by $\mathfrak q^2$ — pushed forward to $\mathbb{Q}$ coefficientwise, and $\lambda_q$ is obtained from it by the exponent-scaling ring homomorphism $\mathfrak q \mapsto \mathfrak q^{q}$. Working inside the field $L((\mathfrak q))$ of Laurent series over $L$, write $\lambda_L$ for the coefficientwise image of `lambdaInt` and $\lambda_{L,q}$ for its exponent-scaling by $q$. The assertion is that the minimal polynomial of $\lambda_{L,q}$ over the intermediate field $L(\lambda_L)$ equals the image of $\Psi$ under the coefficientwise ring homomorphism $\mathbb{Z}[X] \to L(\lambda_L)$ sending $X$ to $\lambda_L$; that is, $\Psi(\lambda_L, Y)$ is the minimal polynomial of $\lambda_{L,q}$ over $L(\lambda_L)$.
--
--   This is the level-two modular equation in the form of an irreducibility-and-degree statement: it says that the classical modular polynomial relating the $\lambda$-series at $\mathfrak q$ and at $\mathfrak q^{q}$ is irreducible over $L(\lambda)$, so that $[L(\lambda,\lambda_q):L(\lambda)] = q+1 = \psi(4q)/\psi(4)$. It underlies the degree and reciprocity properties of the packaged polynomial $\Psi$ and the construction of the local node rings attached to the $\lambda$-tower.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_minpoly_lambdaNModC_eq.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaModularPolynomialData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.minpoly_lambdaNModC_eq (L : Type*) [Field L] [Algebra ℚ L]
    (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) (data : LambdaModularPolynomialData q) :
    minpoly (↥(IntermediateField.adjoin L ({lambdaModC L} : Set (LaurentSeries L)))) (lambdaNModC L q) =
      data.Ψ.map (Polynomial.eval₂RingHom
        (Int.castRingHom (↥(IntermediateField.adjoin L ({lambdaModC L} : Set (LaurentSeries L)))))
        ⟨lambdaModC L, IntermediateField.mem_adjoin_simple_self L (lambdaModC L)⟩) := by sorry
