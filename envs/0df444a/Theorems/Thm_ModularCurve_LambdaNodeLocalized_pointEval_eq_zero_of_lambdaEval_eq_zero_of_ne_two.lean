-- Prove2me | Theorems.Thm_ModularCurve_LambdaNodeLocalized_pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two
-- name    : ModularCurve.LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/b4380d9e-da73-5416-afc2-9934428a2444
-- title:
--   Relations between the λ-series vanish at (l,l^q) mod q
-- statement:
--   Let $q$ be a prime (supplied as a `Fact`) with $q \neq 2$, let $A$ be a valuation subring of $\overline{\mathbb Q} =$ `AlgebraicClosure ℚ`, let $k$ be a field of characteristic $q$, let $\mathrm{red} \colon A \to k$ be a ring homomorphism, and let $l \in k$ satisfy $l^{q^2} = l$. Let $K$ be an intermediate field of $\overline{\mathbb Q}/\mathbb Q$ and write $A_0 =$ `coeffSubring A K` for the subring $A \cap K$ of $\overline{\mathbb Q}$. Let $s$ be a polynomial in two variables $X_0, X_1$ with coefficients in $A_0$. Assume that $s$ is a relation between the two $\lambda$-series, i.e. that `lambdaEval q A₀ s` vanishes: here `lambdaEval` is the ring homomorphism from $A_0[X_0,X_1]$ to the Laurent series field over $\overline{\mathbb Q}$ which embeds coefficients as constant series via `constSeries`, sends $X_0$ to the series `lambdaModC (AlgebraicClosure ℚ)` obtained by base change along $\mathbb Z \to \overline{\mathbb Q}$ from the integral series `lambdaInt`, and sends $X_1$ to `lambdaNModC (AlgebraicClosure ℚ) q`, the image of the former under the project's nome-substitution operator `qExpand` at level $q$. The conclusion is that `pointEval A₀ (redRestrict red K) l (l ^ q) s` $= 0$ in $k$: that is, evaluating $s$ at $(X_0,X_1) = (l, l^q)$ after reducing its coefficients by $\mathrm{red}$ restricted to $A_0 \subseteq A$ gives zero.
--
--   This is the level-two (Legendre $\lambda$) form of the classical statement that, modulo $q$, the modular equation relating a modular function and its $q$-th nome transform becomes the Kronecker congruence, so that every integral relation between the two $\lambda$-expansions vanishes on the graph of the $q$-power map in characteristic $q$. It is used in the analysis of the local structure of the $\lambda$-line at a node of the special fibre, for instance in the identification of completed local rings with a crossing model and in the description of the maximal ideals of the localisation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LambdaNodeLocalized_pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two.lean

import Mathlib
import Definitions.Def_ModularCurve_LambdaNodeLocalized
import Definitions.Def_ModularCurve_NodeDescent

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option autoImplicit false

open ModularCurve ModularCurve.NodeLocalized ModularCurve.LambdaNodeLocalized

theorem ModularCurve.LambdaNodeLocalized.pointEval_eq_zero_of_lambdaEval_eq_zero_of_ne_two
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] (red : A →+* k) (l : k) (hl2 : l ^ (q ^ 2) = l)
    (K : IntermediateField ℚ (AlgebraicClosure ℚ))
    (s : MvPolynomial (Fin 2) ↥(coeffSubring A K))
    (hs : lambdaEval q (coeffSubring A K) s = 0) :
    NodeLocalized.pointEval (coeffSubring A K) (redRestrict red K) l (l ^ q) s = 0 := by sorry
