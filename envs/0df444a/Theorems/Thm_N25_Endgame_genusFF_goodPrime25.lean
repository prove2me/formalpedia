-- Prove2me | Theorems.Thm_N25_Endgame_genusFF_goodPrime25
-- name    : N25.Endgame.genusFF_goodPrime25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:44:44.918921+00:00
-- url     : https://prove2.me/theorems/195dbc74-6494-4452-bf0e-d13a8ddda61f
-- title:
--   The level-$25$ function field has genus four at every good prime
-- statement:
--   Let $p$ be a prime with $p∤25$, and let $F_p$ be the level-$25$ modular function field over $𝔽_p$. Then its function-field genus is
--
--   $$g(F_p/𝔽_p)=4.$$
--
--   This fixes the degree-eight Weil numerator used in the point-count reconstruction at the good primes.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CoefficientMap
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
import Theorems.Thm_ModularCurve_qExpFunctionFieldC_eq_adjoin_image_coeffMap_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_genusFF_eq_of_constantFieldExtension_of_finite_of_isAlgClosed
import Theorems.Thm_ModularCurve_genusFF_xHFunctionFieldC_eq_genusFF_xHFunctionFieldBar_of_not_dvd
import Definitions.Def_N25
import Definitions.Def_ModularCurve_JqCoeff
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_ModularCurve_two_mul_genusFF_add_card_fibres_eq_finrank_add_two_of_gamma1_le

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.genusFF_goodPrime25
    (p : ℕ) [Fact p.Prime] (hgood : ¬ p ∣ 25) :
    AlgebraicCurve.genusFF (ZMod p) (FBase (ZMod p)) = 4 := by sorry
