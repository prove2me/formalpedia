-- Prove2me | Theorems.Thm_ModularCurve_coeffRed_lambdaEval
-- name    : ModularCurve.coeffRed_lambdaEval
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.598281+00:00
-- url     : https://prove2.me/theorems/8b79708c-a4d6-5932-90c3-c4d7a5914f28
-- title:
--   Coefficientwise reduction commutes with evaluating at λ-expansions
-- statement:
--   Let $N$ be a nonzero natural number, $L$ a field, $A \subseteq L$ a subring, $k$ a field and $\mathrm{red} \colon A \to k$ a ring homomorphism; let $p \in A[X_0,X_1]$ be a polynomial in two variables over $A$. Write $\lambda_{\mathrm{int}} \in \mathbb{Z}(\!(q)\!)$ for the integral Laurent series `lambdaInt`, $\lambda_L =$ `lambdaModC L` for its coefficientwise image under $\mathbb{Z} \to L$, and $\lambda_{L,N} =$ `lambdaNModC L N` for the series obtained from $\lambda_L$ by multiplying all exponents by $N$ (the map `qExpand L N`). Let `lambdaEval N A p` be the image of $p$ under the ring homomorphism $A[X_0,X_1] \to L(\!(q)\!)$ sending a constant $a \in A$ to the constant series $a$ and $X_0, X_1$ to $\lambda_L, \lambda_{L,N}$. The assertion is that this series lies in the subring `integralCoeffs A` of those Laurent series over $L$ all of whose coefficients lie in $A$ — the membership being part of the existential statement — and that its image under the coefficientwise reduction homomorphism `coeffRed A red` $\colon$ `integralCoeffs A` $\to k(\!(q)\!)$ equals the value at $p$ of the evaluation homomorphism with coefficient map $a \mapsto \mathrm{red}(a)$ viewed as a constant series in $k(\!(q)\!)$ and with $X_0, X_1$ sent to $\lambda_k$ and $\lambda_{k,N}$.
--
--   This is the compatibility of reduction of coefficients with evaluation of a two-variable polynomial relation at the $q$-expansions of the Legendre $\lambda$-parameter at levels $1$ and $N$: a polynomial relation over $A$ between the two expansions reduces to the corresponding relation over $k$. It is used to transfer vanishing of such a relation from characteristic zero to the reduced setting, in [`ModularCurve.LambdaNodeLocalized.eval2_branch_eq_zero_of_lambdaEval_eq_zero`](thm.html#ModularCurve.LambdaNodeLocalized.eval2_branch_eq_zero_of_lambdaEval_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_coeffRed_lambdaEval.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_CharPReduction

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.LambdaNodeLocalized ModularCurve.CharPReduction

theorem ModularCurve.coeffRed_lambdaEval (N : ℕ) [NeZero N] {L : Type*} [Field L] (A : Subring L)
    {k : Type*} [Field k] (red : A →+* k) (p : MvPolynomial (Fin 2) A) :
    ∃ hp : LambdaNodeLocalized.lambdaEval N A p ∈ CharPReduction.integralCoeffs A,
      CharPReduction.coeffRed A red ⟨LambdaNodeLocalized.lambdaEval N A p, hp⟩
        = MvPolynomial.eval₂Hom ((algebraMap k (LaurentSeries k)).comp red) ![lambdaModC k, lambdaNModC k N] p := by sorry
