-- Prove2me | Theorems.Thm_N25_cusp_width_twentyFive_card_le_five
-- name    : N25.cusp_width_twentyFive_card_le_five
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:50.070396+00:00
-- url     : https://prove2.me/theorems/fead778b-9aa1-459e-8850-12fe4fed233b
-- title:
--   There are at most five geometric cusps of width $25$
-- statement:
--   Let $j_{25}$ be the modular $j$-function on the geometric level-$25$ function field. The set of places at which its order is $-25$ is finite and has cardinality at most five:
--
--   $$\bigl|\{P:\operatorname{ord}_P(j_{25})=-25\}\bigr|\le5.$$
--
--   This bounds the Fricke cusp orbit before proving that five such places actually occur.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Endgame
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_natCard_fibres_jqModC_eq_natCard_doubleCoset_of_finrank_eq_index
import Theorems.Thm_AlgebraicCurve_exists_finset_sum_neg_ord_eq_finrank_of_isAlgClosed

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open ModularCurve AlgebraicCurve
open N25
open N25.Endgame

theorem N25.cusp_width_twentyFive_card_le_five :
    Finite {P : GPlace // P.ord (emb25 j25) = -25} ∧
      Nat.card {P : GPlace // P.ord (emb25 j25) = -25} ≤ 5 := by sorry
