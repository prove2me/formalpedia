-- Prove2me | Theorems.Thm_ModularCurve_finrank_adjoin_lambdaModC_adjoin_lambdaNModC
-- name    : ModularCurve.finrank_adjoin_lambdaModC_adjoin_lambdaNModC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.414366+00:00
-- url     : https://prove2.me/theorems/ade21da9-6883-5486-8d4c-fd5df919e56d
-- title:
--   Degree q+1 of λ(qτ) over L(λ), λ the X₀(4) Hauptmodul
-- statement:
--   Let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, let $q$ be a prime and assume $q \neq 2$. Inside the field $\mathrm{LaurentSeries}\,L$ of formal Laurent series over $L$, consider the element `lambdaModC L`, obtained by applying the coefficientwise map induced by $\mathbb{Z} \to L$ to the integral Laurent series `lambdaInt`, which is the product of the monomial $\mathrm{HahnSeries.single}\,1\,1$ (the variable), the eighth power of the $\eta$-product power series `etaProd`, the image of its sixteenth power under `qExpand` with parameter $4$, and the image of `dedekindEtaUnitInv` under `qExpand` with parameter $2$; here `qExpand` with parameter $N$ is the ring homomorphism multiplying all exponents by $N$. Further set `lambdaNModC L q` $=$ `qExpand L q (lambdaModC L)`, the series obtained from `lambdaModC L` by multiplying all exponents by $q$. The assertion is that the intermediate field of $\mathrm{LaurentSeries}\,L$ generated over the intermediate field $L(\mathrm{lambdaModC}\,L)$ by the single element `lambdaNModC L q` has degree exactly $q + 1$ as a module over $L(\mathrm{lambdaModC}\,L)$.
--
--   In classical terms, $\lambda$ is the Hauptmodul $\eta(\tau)^8\eta(4\tau)^{16}/\eta(2\tau)^{24}$ of $X_0(4)$ and the statement is that its transform $\lambda(q\tau)$ has degree $[\Gamma_0(4):\Gamma_0(4q)] = \psi(4q)/\psi(4) = q+1$ over $L(\lambda)$, for $q$ an odd prime. It is the degree input for the construction of the level-$4$ modular polynomial $\Psi_q(\lambda, Y)$ as the minimal polynomial of $\lambda(q\tau)$ over $L(\lambda)$, and is cited by the results on the coefficients of that minimal polynomial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_finrank_adjoin_lambdaModC_adjoin_lambdaNModC.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.finrank_adjoin_lambdaModC_adjoin_lambdaNModC
    (L : Type*) [Field L] [Algebra ℚ L] (q : ℕ) [Fact q.Prime] (hq2 : q ≠ 2) :
    Module.finrank (↥(IntermediateField.adjoin L ({lambdaModC L} : Set (LaurentSeries L))))
      (↥(IntermediateField.adjoin (↥(IntermediateField.adjoin L ({lambdaModC L} : Set (LaurentSeries L))))
        ({lambdaNModC L q} : Set (LaurentSeries L)))) = q + 1 := by sorry
