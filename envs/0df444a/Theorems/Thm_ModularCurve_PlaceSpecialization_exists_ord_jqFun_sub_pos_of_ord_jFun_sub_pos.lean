-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jqFun_sub_pos_of_ord_jFun_sub_pos
-- name    : ModularCurve.PlaceSpecialization.exists_ord_jqFun_sub_pos_of_ord_jFun_sub_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/83b1c6b2-aa8d-5a85-ba88-cfaaec46914b
-- title:
--   A place with an A-value of j has one of j_q
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $red : A \to k$, together with modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ vanishing on the pair $(j, j_q)$ of $q$-expansions), a Kronecker congruence `hKr` asserting that the reduction of $\Phi$ modulo $q$ equals $(C X^{q} - X)(C X - X^{q})$, and integrality hypotheses `hα`, `hβ` saying that the two degeneracy embeddings `heckeAlphaBar` and `heckeBetaBar` from level $1$ to level $1 \cdot q$ over $\overline{\mathbb Q}$ are integral ring maps. Let $P$ be a place specialisation datum of level $N = 1$ for these data, i.e. a structure providing a map `sp` from places of $\overline{\mathbb Q}\cdot F_{1}$ to places of the characteristic-$q$ function field `modularFunctionFieldC k 1`, a homomorphism `spPic0` on degree-zero divisor class groups, and clauses relating orders of $j$, of $j$ composed with $q \mapsto q^{N}$, and of their reductions. Let $W$ be a place of $\overline{\mathbb Q}\cdot F_{1 \cdot q}$, that is, a proper valuation subring containing all constants and whose local ring is a principal ideal ring, with $\mathrm{ord}_W = -\log$ of its adic valuation. Assume there is $a \in A$ with $\mathrm{ord}_W(j - a) > 0$, where $j$ is the element `jFun` of $\overline{\mathbb Q}\cdot F_{1\cdot q}$ given by the coefficientwise embedding of the $q$-expansion of $j$ and $a$ is viewed as a constant. Then there exists $y \in A$ with $\mathrm{ord}_W(j_q - y) > 0$, where $j_q$ is the element `jqFun` obtained from the Laurent series $j$ by the substitution $q \mapsto q^{1\cdot q}$.
--
--   This is the value-integrality statement along the modular correspondence at level $q$: a place of the level-$q$ modular function field at which $j$ takes a value in the valuation subring $A$ also assigns a value in $A$ to the second coordinate $j_q$. It is used in the analysis of level-one prolongation pairs, in particular in the construction of splitting data and of admissible representatives of divisor classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_ord_jqFun_sub_pos_of_ord_jFun_sub_pos.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneProlongationPair

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.exists_ord_jqFun_sub_pos_of_ord_jFun_sub_pos
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) (a : A)
    (ha : 0 < W.ord (PlaceSpecialization.jFun (q := q)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ))) :
    ∃ y : A, 0 < W.ord (PlaceSpecialization.jqFun (q := q)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (y : AlgebraicClosure ℚ)) := by sorry
