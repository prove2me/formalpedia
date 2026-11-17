-- Prove2me | Theorems.Thm_N25_Endgame_xHGood_eq_adjoin_units25
-- name    : N25.Endgame.xHGood_eq_adjoin_units25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:59:45.237203+00:00
-- url     : https://prove2.me/theorems/b7cea870-3042-4302-ac67-d411cbb5ea51
-- title:
--   The two modular units generate in every field of characteristic $2$ or $3$
-- statement:
--   Let $p$ be prime with $p=2$ or $p=3$, let $K$ be any field of characteristic $p$, let $F_K$ be the level-$25$ modular function field over $K$, and let $U_0,U_1∈F_K$ be the first two modular units. Then
--
--   $$K(U_0,U_0/U_1)=F_K.$$
--
--   This extends the prime-field generation theorem to all coefficient fields in the two good characteristics.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitLaurentField
import Definitions.Def_N25_CoefficientMap
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Definitions.Def_N25_Units
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_UnitOrders
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Theorems.Thm_AlgebraicCurve_Place_transcendental_of_ord_ne_zero
import Theorems.Thm_AlgebraicCurve_Divisor_degree_eq_finrank_adjoin_of_eq_max_neg_ord
import Theorems.Thm_AlgebraicCurve_IsCurveOver_finiteDimensional_adjoin_simple_of_transcendental_of_essFiniteType
import Theorems.Thm_ValuationSubring_exists_isFrobeniusAt_rat
import Theorems.Thm_ValuationSubring_charP_residueField_of_liesOverPrime
import Theorems.Thm_ModularCurve_exists_transcendental_and_reductionInputsQExpModL_gammaH_of_not_dvd
import Definitions.Def_N25_UnitSeries
import Theorems.Thm_ModularCurve_relfinrank_adjoin_image_coeffMap_eq_relfinrank_of_le

open N25
open N25.Endgame
open N25 AlgebraicCurve

theorem N25.Endgame.xHGood_eq_adjoin_units25
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3)
    (K : Type*) [Field K] [CharP K p] :
    IntermediateField.adjoin K
      ({U25C K 0, U25C K 0 / U25C K 1} : Set (FBase K)) = ⊤ := by sorry
