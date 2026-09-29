-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValuation_jQFun_eq_pow_or_eq_pow_of_kroneckerCongruence
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.hasValuation_jQFun_eq_pow_or_eq_pow_of_kroneckerCongruence
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:45.66333+00:00
-- url     : https://prove2.me/theorems/fb2b88f8-64e2-559c-acf4-9dc42ce0f27a
-- title:
--   Valuations of j and j_q at a place over the cusps
-- statement:
--   Let $q$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ whose valuation satisfies $A.\mathrm{valuation}(q) < 1$, so that $q$ lies in the maximal ideal of $A$. Let $N \geq 1$, and let `data` be a modular polynomial datum of level $q$, that is, a monic bivariate polynomial $\Phi$ over $\mathbb{Z}$ of degree $\psi(q)$ annihilating the pair $(j, j_{q})$ of $q$-expansions, and assume the Kronecker congruence `KroneckerCongruence q data`: the reduction of $\Phi$ modulo $q$ in both variables equals $(C(X)^{q} - X)\,(C(X) - X^{q})$. Let $W$ be a place of the function field $\mathrm{modularFunctionFieldBar}(Nq)$ over $\overline{\mathbb{Q}}$, i.e. a proper valuation subring of that field containing the image of $\overline{\mathbb{Q}}$ and whose valuation ring is a principal ideal ring. Let $\gamma, \gamma'$ lie in the value group of $A$ with $1 < \gamma'$. Assume `jFun N q`, the element of the function field given by the $q$-expansion of $j$, has valuation $\gamma$ at $W$ relative to $A$, and `jQFun N q`, given by the $q$-expansion $j(\mathfrak{q}^{q})$, has valuation $\gamma'$; here having valuation $\delta$ means that there is $a \in \overline{\mathbb{Q}}$ with $A.\mathrm{valuation}(a) = \delta$ such that the function lies in the valuation ring of $W$ and its residue is the image of $a$ in the residue field of $W$. Then either $\gamma' = \gamma^{q}$ or $\gamma = \gamma'^{q}$.
--
--   This is the local consequence of the Kronecker congruence $\Phi_q(X,Y) \equiv (X^q - Y)(X - Y^q) \bmod q$ at a place lying over the cuspidal region of $X_0(Nq)$: one of the two depths of $j$ and of its $q$-transform is $q$ times the other, the two alternatives recording the orientation of the corresponding edge of the level-$q$ Hecke correspondence. It feeds the identification of the second reduction map with the Frobenius twist of the first at places where the order of $j_q$ is non-negative, in the analysis of the reduction of modular curves at $q$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_hasValuation_jQFun_eq_pow_or_eq_pow_of_kroneckerCongruence.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_PlaceDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.hasValuation_jQFun_eq_pow_or_eq_pow_of_kroneckerCongruence
    {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ)) (hqA : A.valuation (q : AlgebraicClosure ℚ) < 1)
    {N : ℕ} [NeZero N] {data : ModularPolynomialData q} (hKr : KroneckerCongruence q data)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q)))
    {γ γ' : A.ValueGroup} (hγ' : 1 < γ')
    (hj : W.HasValuation A (jFun N q) γ) (hjq : W.HasValuation A (jQFun N q) γ') :
    γ' = γ ^ q ∨ γ = γ' ^ q := by sorry
