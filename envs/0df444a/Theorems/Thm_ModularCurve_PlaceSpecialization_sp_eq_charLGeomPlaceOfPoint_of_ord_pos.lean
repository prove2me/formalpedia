-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_sp_eq_charLGeomPlaceOfPoint_of_ord_pos
-- name    : ModularCurve.PlaceSpecialization.sp_eq_charLGeomPlaceOfPoint_of_ord_pos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/aafb63da-b2c9-553c-9db2-745fe40d714b
-- title:
--   Specialisation of a place where j-b vanishes
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red}\colon A\to k$. Fix further a `ModularPolynomialData` $q$, i.e. a monic $\Phi\in\mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j,j_q)$, together with the hypothesis `KroneckerCongruence` that the reduction of $\Phi$ modulo $q$ equals $(C(X)^q-X)\,(C(X)-X^q)$, and the two hypotheses that the base-changed Hecke embeddings `heckeAlphaBar` and `heckeBetaBar` from level $1$ to level $q$ over $\overline{\mathbb Q}$ are integral ring maps. Let $P$ be a term of the structure `PlaceSpecialization` for these data at level $N=1$: it provides a map $\mathrm{sp}$ from places of the field $\mathrm{modularFunctionFieldBar}\,1$ (the base change to $\overline{\mathbb Q}$, inside Laurent series over $\overline{\mathbb Q}$, of the full level-one modular function field) to places of $\mathrm{modularFunctionFieldC}\,k\,1$, a homomorphism on degree-zero divisor class groups, and the coordinate clauses, among them `d0_j`: for every place $w$ and every $a\in A$, if $\mathrm{ord}_w(j-a)>0$ then $\mathrm{ord}_{\mathrm{sp}\,w}(\bar j-\mathrm{red}\,a)>0$. Here a place is a proper valuation subring of the function field containing the constants and being a principal ideal ring, and $\mathrm{ord}$ is the associated normalised additive valuation. Let $v$ be a place of $\mathrm{modularFunctionFieldBar}\,1$, let $b\in A$, and assume $\mathrm{ord}_v(j-b)>0$, where $j$ denotes the element of that field given by the coefficientwise image of the Laurent series `jq` and $b$ is mapped in by the structure map. Then $\mathrm{sp}(v)=\mathrm{charLGeomPlaceOfPoint}\,k\,(\mathrm{red}\,b)$, the place of $\mathrm{modularFunctionFieldC}\,k\,1$ obtained by transporting, along the identification of that field with the rational function field $k(j)$, the place attached to the irreducible polynomial $X-\mathrm{red}\,b$.
--
--   This pins down an abstract level-one place specialisation on the locus of integral $j$-invariant: a place of $\overline{\mathbb Q}(j)$ centred at $j=b$ with $b$ in the valuation ring $A$ goes to the place $j=\mathrm{red}\,b$ of $k(j)$. It is used in the identification of the reductions of places of the level-$q$ modular curve, for instance in the divisor-law and strict-type analyses of prolongation pairs and in showing that the specialised residue data lie over an algebraically closed field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_sp_eq_charLGeomPlaceOfPoint_of_ord_pos.lean

import Mathlib
import Definitions.Def_ModularCurve_PlaceSpecialization
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.sp_eq_charLGeomPlaceOfPoint_of_ord_pos
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar 1)) (b : A)
    (hv : 0 < v.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar 1) (b : AlgebraicClosure ℚ))) :
    P.sp v = charLGeomPlaceOfPoint k (red b) := by sorry
