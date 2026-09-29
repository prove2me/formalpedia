-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_not_isStrictTypeOne_and_isStrictTypeTwo
-- name    : ModularCurve.PlaceSpecialization.not_isStrictTypeOne_and_isStrictTypeTwo
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/276e3cb7-909b-51e7-8e21-d9002e2e679b
-- title:
--   Strict type one and strict type two are exclusive
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} \colon A \to k$. Let `data` be a `ModularPolynomialData q`, i.e. a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ vanishing on the pair $(j, j_q)$ of $q$-expansions, and let `hKr` be a proof of the Kronecker congruence for it: the reduction of $\Phi$ modulo $q$ equals $(C(X)^q - X)\,(C(X) - X^q)$. Let `hα`, `hβ` assert the integrality of the two degeneracy embeddings `heckeAlphaBar`, `heckeBetaBar` from level $1$ to level $1 \cdot q$ over $\overline{\mathbb Q}$, and let $P$ be a `PlaceSpecialization A q 1 data hKr k red hα hβ`, i.e. a specialisation datum carrying places of the level-one function field over $\overline{\mathbb Q}$ to places over $k$ together with a homomorphism on degree-zero divisor class groups and the order-comparison conditions for $j$ and $j_N$. Let $W$ be a place of `modularFunctionFieldBar (1 * q)` over $\overline{\mathbb Q}$, and write $\varphi$ for `frobOnPlacesGeomLevel k 1 data hKr` and $\mathrm{red}_1 W$, $\mathrm{red}_2 W$ for the two places of `modularFunctionFieldC k 1` attached to $W$ by $P$. Then it is not the case that both ($\varphi(\mathrm{red}_1 W) = \mathrm{red}_2 W$ and $\varphi^2(\mathrm{red}_1 W) \neq \mathrm{red}_1 W$) and ($\mathrm{red}_1 W = \varphi(\mathrm{red}_2 W)$ and $\varphi^2(\mathrm{red}_2 W) \neq \mathrm{red}_2 W$) hold.
--
--   The statement records that the strict type one and strict type two loci in the fibre of $X_0(q)$ at $q$ are disjoint, so that the two parts of a divisor built from them have disjoint support. It is used in the analysis of the level-one gluing datum, in particular by the results on good representatives for prolongation pairs and by the charts lemma for multiplicative coverings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_not_isStrictTypeOne_and_isStrictTypeTwo.lean

import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SupersingularNodes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000

open AlgebraicCurve ModularCurve

theorem ModularCurve.PlaceSpecialization.not_isStrictTypeOne_and_isStrictTypeTwo
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q]
    {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q}
    {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ) (W : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q))) :
    ¬ (P.IsStrictTypeOne W ∧ P.IsStrictTypeTwo W) := by sorry
