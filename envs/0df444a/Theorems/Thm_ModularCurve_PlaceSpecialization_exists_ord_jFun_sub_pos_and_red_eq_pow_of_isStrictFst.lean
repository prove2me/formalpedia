-- Prove2me | Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jFun_sub_pos_and_red_eq_pow_of_isStrictFst
-- name    : ModularCurve.PlaceSpecialization.exists_ord_jFun_sub_pos_and_red_eq_pow_of_isStrictFst
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.056571+00:00
-- url     : https://prove2.me/theorems/996b53e7-653f-5e9b-b838-28512a18d670
-- title:
--   Strict first-kind places reduce onto the Frobenius graph
-- statement:
--   Fix a prime $p$, a valuation subring $A$ of $\overline{\mathbb Q}$, an algebraically closed field $k$ of characteristic $p$ and a ring homomorphism $\mathrm{red} : A \to k$. Let `data` consist of a monic $\Phi \in \mathbb Z[X][Y]$ of degree $\psi(p)$ annihilating the pair $(j, j_p)$, let `hKr` assert the Kronecker congruence that the bivariate reduction of $\Phi$ modulo $p$ factors as $(C X^p - X)(C X - X^p)$, and let `hα`, `hβ` assert that the two Hecke embeddings `heckeAlphaBar`, `heckeBetaBar` of the level-$1$ into the level-$p$ base-changed modular function field are integral ring homomorphisms. Let $P$ be a `PlaceSpecialization` for these data, i.e. a specialisation of places of `modularFunctionFieldBar 1` to places of `modularFunctionFieldC k 1` together with a map on degree-zero divisor class groups and the stated compatibilities for $j$ and $j_p$. Let $V$ be a place of `modularFunctionFieldBar (1 * p)` (a proper valuation subring, principal, containing $\overline{\mathbb Q}$) satisfying `P.IsStrictFst`: the geometric-level Frobenius on places carries the first reduction of $V$ (restriction along `heckeAlphaBar`, then $P$'s specialisation) to its second reduction (the same with `heckeBetaBar`), and the twofold Frobenius iterate does not fix the first reduction. Then there are $a, b \in A$ with $\mathrm{ord}_V(\,j - a\,) > 0$ and $\mathrm{ord}_V(\,j_p - b\,) > 0$, where $j$ and $j_p$ denote `jFun` and `jqFun`, the coefficient embeddings of the $q$-expansions of $j$ and of $j$ with $q \mapsto q^{p}$, such that $\mathrm{red}\,b = (\mathrm{red}\,a)^p$ and $(\mathrm{red}\,a)^{p^2} \neq \mathrm{red}\,a$.
--
--   This is the function-field-theoretic half of the statement that the reduction modulo $p$ of $X_0(p)$ consists of the graph of Frobenius and its transpose: a place which is strict of the first kind has $A$-integral coordinates $j, j_p$ whose reductions lie on the graph of Frobenius, and whose $j$-invariant is not in $\mathbb F_{p^2}$. It feeds the germ-level statement [`ModularCurve.DRModelPackage.exists_germ_jq_sub_pow_and_stalkSpecializes_mem_maximalIdeal_of_swap`](thm.html#ModularCurve.DRModelPackage.exists_germ_jq_sub_pow_and_stalkSpecializes_mem_maximalIdeal_of_swap).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_PlaceSpecialization_exists_ord_jFun_sub_pos_and_red_eq_pow_of_isStrictFst.lean

import Mathlib
import Definitions.Def_ModularCurve_GlueData
import Definitions.Def_ModularCurve_LevelOneGlueData
import Definitions.Def_ModularCurve_LevelOneProlongationPair
import Definitions.Def_ModularCurve_SpecializeModuli
import Definitions.Def_AlgebraicCurve_RatFuncPlaceInfty
import Definitions.Def_ModularCurve_HeckeOperator
import Theorems.Thm_ModularCurve_PlaceSpecialization_redFst_eq_charLGeomPlaceOfPoint_iff
import Theorems.Thm_ModularCurve_eq_charLGeomPlaceOfPoint_or_eq_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceOfPoint
import Theorems.Thm_ModularCurve_frobOnPlacesGeomLevel_charLGeomPlaceEquiv_placeInfty
import Theorems.Thm_ModularCurve_PlaceSpecialization_redSnd_eq_charLGeomPlaceOfPoint_of_ord_pos
import Theorems.Thm_ModularCurve_PlaceSpecialization_exists_ord_jqFun_sub_pos_of_ord_jFun_sub_pos
import Theorems.Thm_ModularCurve_heckeBetaBar_coeffEmb

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve ModularCurve.PlaceSpecialization

set_option maxHeartbeats 400000 in

theorem ModularCurve.PlaceSpecialization.exists_ord_jFun_sub_pos_and_red_eq_pow_of_isStrictFst
    {p : ℕ} [Fact p.Prime] {A : ValuationSubring (AlgebraicClosure ℚ)}
    {k : Type} [Field k] [CharP k p] [IsAlgClosed k] {red : A →+* k}
    {data : ModularPolynomialData p} {hKr : KroneckerCongruence p data}
    {hα : HeckeAlphaBarIntegral (AlgebraicClosure ℚ) 1 p} {hβ : HeckeBetaBarIntegral (AlgebraicClosure ℚ) 1 p}
    (P : PlaceSpecialization A p 1 data hKr k red hα hβ)
    (V : Place (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p))) (hV : P.IsStrictFst V) :
    ∃ a b : A,
      0 < V.ord (PlaceSpecialization.jFun (q := p) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (a : (AlgebraicClosure ℚ))) ∧
      0 < V.ord (PlaceSpecialization.jqFun (q := p) - algebraMap (AlgebraicClosure ℚ) ↥(modularFunctionFieldBar (1 * p)) (b : (AlgebraicClosure ℚ))) ∧
      red b = red a ^ p ∧ red a ^ (p ^ 2) ≠ red a := by sorry
