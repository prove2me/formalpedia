-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_placeInfty_of_forall_ord_le_zero
-- name    : ModularCurve.PlaceSpecialization.redFst_eq_placeInfty_of_forall_ord_le_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/366a7bd6-f494-55d5-8b7e-856cb2f4c5f3
-- title:
--   Places with no integral j-value reduce to the cusp
-- statement:
--   Fix a prime $q$, a valuation subring $A$ of $\overline{\mathbb{Q}}$, a field $k$ of characteristic $q$ and a ring homomorphism $\mathrm{red} \colon A \to k$; fix modular polynomial data `data` for $q$ together with a proof `hKr` that its polynomial $\Phi$ reduces modulo $q$ to $(X^q - Y)(X - Y^q)$ in the bivariate sense of `KroneckerCongruence`, and proofs `hα`, `hβ` that the two level-raising maps `heckeAlphaBar` and `heckeBetaBar` from level $1$ to level $q$ over $\overline{\mathbb{Q}}$ are integral ring homomorphisms. Let $P$ be a `PlaceSpecialization` packet for $A$, $q$, level $1$, these data and $\mathrm{red}$: in particular it provides a map `sp` from places of the level-one function field over $\overline{\mathbb{Q}}$ to places of the characteristic-$q$ level-one field `modularFunctionFieldC k 1`, together with clauses relating $\mathrm{ord}$ of $j - a$ and of its reduction. Let $W$ be a place (in the sense of the project's `Place`: a proper valuation subring containing the base field whose ring is a principal ideal ring) of `modularFunctionFieldBar (1 * q)`, and assume that $\mathrm{ord}_W(j - a) \le 0$ for every $a \in A$, where $j$ denotes the $q$-expansion `jq` with coefficients pushed into $\overline{\mathbb{Q}}$ and $a$ its image under the structure map. Then $P.\mathrm{redFst}\,W$, namely `sp` applied to the restriction of $W$ along `heckeAlphaBar`, equals the place at infinity of $k(t)$ transported along the isomorphism `ratFuncEquivCharLOneC` to `modularFunctionFieldC k 1`.
--
--   This identifies the first level-one reduction of any place of the level-$q$ curve at which $j$ assumes no $A$-integral value with the cusp of the $j$-line in characteristic $q$; it is the level-$q$ form of the corresponding level-one statement. It feeds the chart and divisor bookkeeping for the special fibre of the level-one gluing, e.g. the multiplicative-covering chart lemmas.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_redFst_eq_placeInfty_of_forall_ord_le_zero.lean

import Mathlib
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

open AlgebraicCurve IsLocalRing ModularCurve

theorem ModularCurve.PlaceSpecialization.redFst_eq_placeInfty_of_forall_ord_le_zero
    {q : ℕ} [Fact q.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type*} [Field k] [CharP k q] [DecidableEq (RatFunc k)] {red : A →+* k}
    {data : ModularPolynomialData q} {hKr : KroneckerCongruence q data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 q} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 q}
    (P : PlaceSpecialization A q 1 data hKr k red hα hβ)
    (W : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * q)))
    (hW : ∀ a : A, W.ord ((⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ)
            (modularFunctionField_le_full (1 * q) (jq_mem (1 * q)))⟩ : modularFunctionFieldBar (1 * q))
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar (1 * q)) (a : AlgebraicClosure ℚ)) ≤ 0) :
    P.redFst W = charLGeomPlaceEquiv k (AlgebraicCurve.RationalFunctionField.placeInfty k) := by sorry
