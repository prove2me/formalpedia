-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_eq_of_restrictAlong_heckeBetaBar_eq_of_hasValuation_jFun_pow
-- name    : ModularCurve.PlaceSpecialization.ProlongationTuple.eq_of_restrictAlong_heckeBetaBar_eq_of_hasValuation_jFun_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:44.572352+00:00
-- url     : https://prove2.me/theorems/6b9b8dc1-4b9a-5521-85d3-3e492a66c9df
-- title:
--   Uniqueness of the place with j of valuation γ^q
-- statement:
--   Let $q$ be a prime and let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ whose (multiplicatively written) valuation satisfies $A.\mathrm{valuation}(q) < 1$, so that $q$ lies in the maximal ideal of $A$. Let $N \geq 1$ with $q \nmid N$, and let `data` be a datum consisting of a monic $\Phi \in \mathbb{Z}[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j(\mathfrak{q}), j(\mathfrak{q}^q))$, assumed to satisfy the Kronecker congruence `hKr`: the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)\,(C(X) - X^q)$. Assume `hβ`, that the second degeneracy algebra map `heckeBetaBar` from the level-$N$ function field $\mathrm{modularFunctionFieldBar}\,N$ to $\mathrm{modularFunctionFieldBar}\,(N q)$ is integral. Let $W, W'$ be places of $\mathrm{modularFunctionFieldBar}\,(Nq)$ over $\overline{\mathbb{Q}}$ (valuation subrings, proper, containing the base field and principal ideal rings) whose restrictions along `heckeBetaBar`, namely the pullbacks of their valuation subrings, agree. Let $\gamma$ be an element of the value group of $A$ with $\gamma > 1$, suppose $W$ gives `jQFun N q` $= j(\mathfrak{q}^q)$ a value in $\overline{\mathbb{Q}}$ of $A$-valuation $\gamma$, and suppose both $W$ and $W'$ give `jFun N q` $= j(\mathfrak{q})$ a value of $A$-valuation $\gamma^q$. Then $W = W'$.
--
--   Over a place of $X_0(N)$ in the region where $j$ has large valuation, the $q+1$ places of $X_0(Nq)$ above it are separated by the Newton polygon of the modular equation of level $q$: exactly one of them, the one corresponding to the canonical subgroup of a Tate curve, has $j$ of valuation the $q$-th power of the valuation of $j(\mathfrak{q}^q)$. This uniqueness statement is used in identifying the second reduction of a place with the Frobenius twist of the first, the geometric form of the Eichler–Shimura congruence relation.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_ProlongationTuple_eq_of_restrictAlong_heckeBetaBar_eq_of_hasValuation_jFun_pow.lean

import Definitions.Def_ModularCurve_ProlongationTuple
import Definitions.Def_AlgebraicCurve_PlaceDepth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve IsLocalRing ModularCurve ModularCurve.PlaceSpecialization

theorem ModularCurve.PlaceSpecialization.ProlongationTuple.eq_of_restrictAlong_heckeBetaBar_eq_of_hasValuation_jFun_pow
    {q : ℕ} [Fact q.Prime] (A : ValuationSubring (AlgebraicClosure ℚ))
    (hqA : A.valuation (q : AlgebraicClosure ℚ) < 1) {N : ℕ} [NeZero N]
    {data : ModularPolynomialData q} (hKr : KroneckerCongruence q data)
    (hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) N q) (hqN : ¬ q ∣ N)
    {W W' : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * q))}
    (hWW' : W.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ
      = W'.restrictAlong (heckeBetaBar (AlgebraicClosure ℚ) N q) hβ)
    {γ : A.ValueGroup} (hγ : 1 < γ) (hW : W.HasValuation A (jQFun N q) γ)
    (hdeep : W.HasValuation A (jFun N q) (γ ^ q)) (hdeep' : W'.HasValuation A (jFun N q) (γ ^ q)) :
    W = W' := by sorry
