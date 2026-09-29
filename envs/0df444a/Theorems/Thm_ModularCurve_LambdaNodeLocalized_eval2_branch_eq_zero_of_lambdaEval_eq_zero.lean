-- Prove2me | Theorems.Thm_ModularCurve_LambdaNodeLocalized_eval2_branch_eq_zero_of_lambdaEval_eq_zero
-- name    : ModularCurve.LambdaNodeLocalized.eval2_branch_eq_zero_of_lambdaEval_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/fc09f1ef-e0bf-501c-a449-fb1324b82fb8
-- title:
--   Branch form of the λ-Kronecker congruence mod q
-- statement:
--   Let $q$ be a prime with $q \neq 2$, let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ`, let $k$ be a field of characteristic $q$ and let $\mathrm{red} \colon A \to k$ be a ring homomorphism. Let $K$ be an intermediate field of $\overline{\mathbb{Q}}/\mathbb{Q}$ and write $A_0 =$ `coeffSubring A K` for the subring $A \cap K$ of $\overline{\mathbb{Q}}$, the intersection of the underlying subring of $A$ with the underlying subring of $K$. Let $s$ be a polynomial in two variables $X_0, X_1$ with coefficients in $A_0$, and suppose that `lambdaEval q A₀ s = 0`, that is, $s$ vanishes when its coefficients are sent into the Laurent series field `LaurentSeries` $\overline{\mathbb{Q}}$ as constants, $X_0$ is sent to `lambdaModC`, the integral $\lambda$-series with coefficients mapped into $\overline{\mathbb{Q}}$, and $X_1$ is sent to `lambdaNModC` at level $q$, the image of `lambdaModC` under `qExpand` at $q$. Then both specialisations of $s$ to one variable over $k$ vanish: applying the ring homomorphism that sends a coefficient $a \in A_0$ to the constant polynomial $\mathrm{red}(a)$ (via `redRestrict`, i.e. $\mathrm{red}$ precomposed with the inclusion $A_0 \hookrightarrow A$) and sends $(X_0, X_1)$ to $(X, X^q)$ gives $0$ in $k[X]$, and likewise with $(X_0, X_1)$ sent to $(X^q, X)$. No finiteness hypothesis is imposed on $K$.
--
--   This is the level-two (Legendre $\lambda$) form of the Kronecker congruence $\Phi_q(X_0,X_1) \equiv (X_0 - X_1^q)(X_0^q - X_1) \pmod q$, in the shape needed for relations: any integral relation satisfied by $\lambda$ and its level-$q$ expansion reduces modulo the residue characteristic to a polynomial vanishing on each of the two branches. It is the input to [`ModularCurve.LambdaNodeLocalized.isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint`](thm.html#ModularCurve.LambdaNodeLocalized.isPrime_span_uniformizer_branches_lambdaLocalizedAtPoint), which identifies the branch ideals at a node of the $\lambda$-model of the modular curve as prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LambdaNodeLocalized_eval2_branch_eq_zero_of_lambdaEval_eq_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_NodeDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized

theorem ModularCurve.LambdaNodeLocalized.eval2_branch_eq_zero_of_lambdaEval_eq_zero
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (s : MvPolynomial (Fin 2) ↥(coeffSubring A K))
    (hs : lambdaEval q (coeffSubring A K) s = 0) :
    MvPolynomial.eval₂Hom (Polynomial.C.comp (redRestrict red K)) ![Polynomial.X, Polynomial.X ^ q] s = 0 ∧
    MvPolynomial.eval₂Hom (Polynomial.C.comp (redRestrict red K)) ![Polynomial.X ^ q, Polynomial.X] s = 0 := by sorry
