-- Prove2me | Theorems.Thm_ModularCurve_LambdaNodeLocalized_exists_ne_zero_lambdaEval_eq_zero
-- name    : ModularCurve.LambdaNodeLocalized.exists_ne_zero_lambdaEval_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/8b493b8b-686a-5f8f-acbd-6e3d68474e45
-- title:
--   Nonzero kernel element of `lambdaEval` from modular polynomial data
-- statement:
--   Fix a natural number $q$ assumed prime. Let `data` be an element of `LambdaModularPolynomialData q`, that is: a polynomial $\Psi \in (\mathbb{Z}[X])[Y]$ which is monic, has degree $q+1$ in $Y$, and satisfies $\Psi = 0$ after the substitution in which each coefficient $c \in \mathbb{Z}[X]$ is sent to the Laurent series over $\mathbb{Q}$ obtained by evaluating $c$ at `lambdaInt` (the integral $\lambda$-series) via `evalAtLambdaInt` and then pushing coefficients along $\mathbb{Z} \to \mathbb{Q}$, while $Y$ is sent to `lambdaNModC ℚ q`, the series $q$-substituted from the $\lambda$-series over $\mathbb{Q}$. Let $L$ be a field with a $\mathbb{Q}$-algebra structure and let $A \subseteq L$ be a subring. The conclusion asserts the existence of a polynomial $P \in A[X_0,X_1]$ in two variables with $P \neq 0$ and `lambdaEval q A P = 0`, where `lambdaEval q A` is the ring homomorphism $A[X_0,X_1] \to L(\!(T)\!)$ sending constants $a \in A$ to their images under $A \hookrightarrow L \to L(\!(T)\!)$, $X_0$ to `lambdaModC L` and $X_1$ to `lambdaNModC L q`. Equivalently: the two Laurent series `lambdaModC L` and `lambdaNModC L q` are algebraically dependent over $A$.
--
--   This records that the kernel of the evaluation map `lambdaEval q A` is nonzero, i.e. that the level-two ($\lambda$, Legendre) modular series and its $q$-substituted companion satisfy a nontrivial polynomial relation with coefficients in any subring $A$ of a field $L$ containing $\mathbb{Q}$. It serves as the input for [`ModularCurve.LambdaNodeLocalized.isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring`](thm.html#ModularCurve.LambdaNodeLocalized.isNoetherianRing_isLocalRing_lambdaLocalizedAtPoint_coeffSubring), where the quotient by this kernel is used to produce the local ring at a node of the relevant modular curve model.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LambdaNodeLocalized_exists_ne_zero_lambdaEval_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_LambdaModularPolynomialData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.LambdaNodeLocalized

theorem ModularCurve.LambdaNodeLocalized.exists_ne_zero_lambdaEval_eq_zero
    {q : ℕ} [Fact q.Prime] (data : LambdaModularPolynomialData q)
    {L : Type*} [Field L] [Algebra ℚ L] (A : Subring L) :
    ∃ P : MvPolynomial (Fin 2) A, P ≠ 0 ∧ lambdaEval q A P = 0 := by sorry
