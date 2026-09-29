-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_of_ord_pos
-- name    : ModularCurve.PlaceSpecialization.redFst_eq_charLGeomPlaceOfPoint_of_ord_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/50bdff73-d0ba-5b9e-ba30-3f975045261f
-- title:
--   First level-one reduction is the place j=b̄
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A \to k$. Fix also modular polynomial data `data` for $q$ (a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$ of $q$-expansions), a proof `hKr` that reducing $\Phi$ modulo $q$ gives $(X^q - Y)(X - Y^q)$ in the bivariate form used there, and proofs `hα`, `hβ` that the two degeneracy inclusions $\bar\alpha,\bar\beta$ from the level-$1$ field into the level-$1\cdot q$ field (base changed to $\overline{\mathbb Q}$ inside Laurent series) are integral ring homomorphisms. Let $P$ be a place specialization of these data: in particular it provides a map $\mathrm{sp}$ from places of $\overline{\mathbb Q}$-modular function field at level $1$ to places of the corresponding field over $k$, together with the clause that $\mathrm{ord}_w(j - a) > 0$ for $a \in A$ implies $\mathrm{ord}_{\mathrm{sp}(w)}(\bar j - \mathrm{red}(a)) > 0$, and the further clauses of that structure. Let $W$ be a place of the level-$1\cdot q$ field over $\overline{\mathbb Q}$ and $b \in A$, and assume $\mathrm{ord}_W\bigl(\bar\alpha(j) - b\bigr) > 0$, where $\mathrm{ord}$ is minus the logarithm of the associated adic valuation and $j$ is the $q$-expansion `jq` with coefficients pushed into $\overline{\mathbb Q}$. Then the first reduction $P.\mathrm{redFst}\,W$, namely $\mathrm{sp}$ applied to the restriction of $W$ along $\bar\alpha$, equals the place of the level-$1$ function field over $k$ corresponding to the point $j = \mathrm{red}(b)$ of the $j$-line.
--
--   This pins down an abstract level-one place specialization on the part of the $j$-line with integral $j$-invariant: a point of the level-$q$ curve whose $j$-coordinate is congruent to $b \in A$ reduces, under the first degeneracy map, to the point $j = \overline{b}$ of the $j$-line over $k$. It is used throughout the level-one gluing arguments, for instance in establishing the divisor laws for prolongation pairs and in locating common uniformisers at level one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_of_ord_pos.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_ModularCurve_LevelOneGlueData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.redFst_eq_charLGeomPlaceOfPoint_of_ord_pos
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q))) (b : A)
    (hW : 0 < W.ord (heckeAlphaBar (AlgebraicClosure ℚ) 1 q (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1)
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (b : AlgebraicClosure ℚ))) :
    P.redFst W = charLGeomPlaceOfPoint k (red b) := by sorry
