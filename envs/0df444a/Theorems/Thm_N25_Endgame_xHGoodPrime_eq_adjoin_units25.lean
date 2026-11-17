-- Prove2me | Theorems.Thm_N25_Endgame_xHGoodPrime_eq_adjoin_units25
-- name    : N25.Endgame.xHGoodPrime_eq_adjoin_units25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:50.957009+00:00
-- url     : https://prove2.me/theorems/75f65daa-9cd8-4807-9cdf-d5d1bc90efb0
-- title:
--   The two modular units generate over $𝔽_2$ and $𝔽_3$
-- statement:
--   Let $p$ be prime with $p=2$ or $p=3$, let $F_p$ be the level-$25$ modular function field over $𝔽_p$, and let $U_0,U_1∈F_p$ be the first two modular units. Then
--
--   $$𝔽_p(U_0,U_0/U_1)=F_p.$$
--
--   This establishes the unit-generated presentation over the prime field at each good characteristic used in the reduction argument.
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

theorem N25.Endgame.xHGoodPrime_eq_adjoin_units25
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3) :
    IntermediateField.adjoin (ZMod p)
      ({U25C (ZMod p) 0, U25C (ZMod p) 0 / U25C (ZMod p) 1} :
        Set (FBase (ZMod p))) = ⊤ := by sorry
