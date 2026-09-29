-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_sp_eq_placeInfty_of_forall_ord_le_zero
-- name    : ModularCurve.PlaceSpecialization.sp_eq_placeInfty_of_forall_ord_le_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/0f557353-7217-51d9-8abd-da38e05a5a69
-- title:
--   Places with non-integral j specialise to j=∞
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb Q}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} : A \to k$; fix data `data` consisting of a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(q)$ annihilating the pair $(j, j_q)$, a witness `hKr` that the reduction of $\Phi$ modulo $q$ equals $(X^q - Y)(X - Y^q)$ in the appropriate bivariate sense, and witnesses `hα`, `hβ` that the level-one Hecke maps $\overline{\alpha}$, $\overline{\beta}$ at $q$ over $\overline{\mathbb Q}$ are integral ring homomorphisms. Let $P$ be a place specialization for these data: in particular it provides a map $\mathrm{sp}$ from places of the level-one function field $\overline{\mathbb Q}(j)$ (realised as the base change to $\overline{\mathbb Q}$ of the full modular function field inside Laurent series, a place being a proper valuation subring containing the constants whose ring is a principal ideal ring) to places of the characteristic-$q$ field `modularFunctionFieldC k 1`, subject to the structure's coordinate clauses. Let $v$ be such a place and assume $\mathrm{ord}_v(j - b) \le 0$ for every $b \in A$, where $j$ denotes the element given by the $q$-expansion `jq` pushed into the base-changed field and $\mathrm{ord}$ is the normalised additive valuation. Then $\mathrm{sp}(v)$ is the place $P_\infty$, namely the image of the degree (infinity) place of $\mathrm{RatFunc}(k)$ under the transport of places along the isomorphism $\mathrm{RatFunc}(k) \simeq$ `modularFunctionFieldC k 1`.
--
--   This is the half of the determination of a level-one place specialization that covers the places where the $j$-coordinate has no centre in $A$: such places reduce to the cusp $j = \infty$ of the $j$-line over $k$. It is used repeatedly in the analysis of prolongation pairs and of divisor laws for the reduction of level-$q$ places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_sp_eq_placeInfty_of_forall_ord_le_zero.lean

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

theorem ModularCurve.PlaceSpecialization.sp_eq_placeInfty_of_forall_ord_le_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (v : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar 1))
    (hv : ∀ b : A, v.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full 1 (jq_mem 1))⟩ : modularFunctionFieldBar 1) - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar 1) (b : AlgebraicClosure ℚ)) ≤ 0) :
    letI := Classical.decEq (RatFunc k)
    P.sp v = charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k) := by sorry
