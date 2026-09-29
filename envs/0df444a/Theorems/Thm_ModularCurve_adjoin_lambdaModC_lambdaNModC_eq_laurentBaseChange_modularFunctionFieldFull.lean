-- Prove2me | Theorems.Thm_ModularCurve_adjoin_lambdaModC_lambdaNModC_eq_laurentBaseChange_modularFunctionFieldFull
-- name    : ModularCurve.adjoin_lambdaModC_lambdaNModC_eq_laurentBaseChange_modularFunctionFieldFull
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/bf654ed9-b47e-54ca-b118-405b504be124
-- title:
--   Adjoining λ and λ(X^q) gives level 4q
-- statement:
--   Let $L$ be a field equipped with an algebra structure over $\mathbb{Q}$ and let $q$ be a natural number which is prime (so in particular nonzero). Work inside the field of Laurent series $L((X))$, realised as Hahn series over $L$ with value group $\mathbb{Z}$. Write $\lambda_L =$ `lambdaModC L` for the coefficientwise image under $\mathbb{Z} \to L$ of the integral Laurent series `lambdaInt`, namely the product of $X$, the eighth power of the eta product `etaProd`, the substitution $X \mapsto X^4$ applied to the sixteenth power of `etaProd`, and the substitution $X \mapsto X^2$ applied to `dedekindEtaUnitInv`; and write `lambdaNModC L q` for the substitution $X \mapsto X^q$ (the `qExpand` operator, induced by multiplication by $q$ on exponents) applied to $\lambda_L$. The assertion is an equality of intermediate fields of $L((X))$ over $L$: the subfield generated over $L$ by the two elements $\lambda_L$ and $\lambda_L(X^q)$ coincides with `laurentBaseChange L (modularFunctionFieldFull (4 * q))`, that is, with the subfield generated over $L$ by the coefficientwise images under $\mathbb{Q} \to L$ of all elements of the subfield of $\mathbb{Q}((X))$ generated over $\mathbb{Q}$ by the series $j(X^d)$ for the nonzero divisors $d$ of $4q$.
--
--   This identifies the base-changed function field of $X_0(4q)$, presented by the $q$-expansions $j(X^d)$ with $d \mid 4q$, as generated over $L$ by the Legendre-type Hauptmodul $\lambda$ of level $4$ together with its substitution $X \mapsto X^q$. It is the generation statement behind the degree computation [`ModularCurve.finrank_adjoin_lambdaModC_adjoin_lambdaNModC`](thm.html#ModularCurve.finrank_adjoin_lambdaModC_adjoin_lambdaNModC) and the identification of the minimal polynomial of $\lambda_L(X^q)$ over $L(\lambda_L)$ in [`ModularCurve.minpoly_lambdaNModC_eq`](thm.html#ModularCurve.minpoly_lambdaNModC_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_adjoin_lambdaModC_lambdaNModC_eq_laurentBaseChange_modularFunctionFieldFull.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaSeries
import Definitions.Def_ModularCurve_LaurentCoeff

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve

theorem ModularCurve.adjoin_lambdaModC_lambdaNModC_eq_laurentBaseChange_modularFunctionFieldFull
    (L : Type*) [Field L] [Algebra ℚ L] (q : ℕ) [Fact q.Prime] :
    IntermediateField.adjoin L ({lambdaModC L, lambdaNModC L q} : Set (LaurentSeries L))
      = laurentBaseChange L (modularFunctionFieldFull (4 * q)) := by sorry
