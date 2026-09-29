-- Prove2me | Theorems.Thm_ModularCurve_LambdaNodeLocalized_lambdaEval_aeval_sixteenth_sub_swap_eq_zero
-- name    : ModularCurve.LambdaNodeLocalized.lambdaEval_aeval_sixteenth_sub_swap_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/49fdfd83-94ee-5e07-a041-e89c47858a6a
-- title:
--   Fricke symmetry of the λ-pair at level two
-- statement:
--   Let $q$ be a prime with $q \neq 2$, let $L$ be a field equipped with a $\mathbb{Q}$-algebra structure, and let $A$ be a subring of $L$. Write `lambdaEval q A` for the ring homomorphism from $A[X_0,X_1]$ (two-variable polynomials with coefficients in $A$) to the Laurent series ring over $L$ that sends a coefficient $a \in A$ to the constant series given by its image in $L$, sends $X_0$ to `lambdaModC L`, the Laurent series obtained from the integral series `lambdaInt` by applying the coefficient map $\mathbb{Z} \to L$, and sends $X_1$ to `lambdaNModC L q`, the series `qExpand L q (lambdaModC L)` obtained from `lambdaModC L` by the $q$-fold substitution in the uniformiser. Let $u \in A$ satisfy $16u = 1$, so that $u$ is the element $1/16$ of $A$, and let $s \in A[X_0,X_1]$ be a polynomial with `lambdaEval q A s` $= 0$. The assertion is that the polynomial obtained from $s$ by the $A$-algebra substitution $X_0 \mapsto u - X_1$, $X_1 \mapsto u - X_0$ again has vanishing image under `lambdaEval q A`.
--
--   This is the level-two form of the Fricke-involution symmetry: since $\tau \mapsto -1/(q\tau)$ interchanges the two $\lambda$-type expansions only up to the anharmonic involution, the relation satisfied by the pair of series is stable not under the bare swap of the two variables but under the swap composed with $x \mapsto 1/16 - x$. It is used in [`ModularCurve.LambdaNodeLocalized.eval2_branch_eq_zero_of_lambdaEval_eq_zero`](thm.html#ModularCurve.LambdaNodeLocalized.eval2_branch_eq_zero_of_lambdaEval_eq_zero) to produce a second vanishing relation from a given one at the node under study.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LambdaNodeLocalized_lambdaEval_aeval_sixteenth_sub_swap_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeLocalized

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.LambdaNodeLocalized

theorem ModularCurve.LambdaNodeLocalized.lambdaEval_aeval_sixteenth_sub_swap_eq_zero
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {L : Type*} [Field L] [Algebra ℚ L] (A : Subring L)
    (u : A) (hu : (16 : A) * u = 1)
    (s : MvPolynomial (Fin 2) A) (hs : lambdaEval q A s = 0) :
    lambdaEval q A
      (MvPolynomial.aeval ![MvPolynomial.C u - MvPolynomial.X 1, MvPolynomial.C u - MvPolynomial.X 0] s) = 0 := by sorry
