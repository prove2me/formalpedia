-- Prove2me | Theorems.Thm_N25_U25_selected_rational_order
-- name    : N25.U25_selected_rational_order
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:44.91461+00:00
-- url     : https://prove2.me/theorems/53daf96b-5535-463d-82ab-16952084634d
-- title:
--   Selected rational cusp orders equal the unit-order table
-- statement:
--   For $i,j∈ℤ/5ℤ$, let $P_j^ℚ$ be the selected rational cusp and $m_{ij}$ the tabulated order. Then $$ord_{P_j^ℚ}(U_i)=m_{ij}.$$ This supplies the selected rational entries of the divisor table.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_UnitOrders
import Definitions.Def_N25_Units
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_BaseChangeGalois
import Definitions.Def_N25_UnitSeries
import Definitions.Def_ModularCurve_LaurentCoeff
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar

set_option autoImplicit false
open N25

theorem N25.U25_selected_rational_order (i j : Fin 5) :
    (N25.Endgame.pQ25 j).ord (U25 i) = unitOrders25 i j := by sorry
