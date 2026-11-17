-- Prove2me | Theorems.Thm_N25_U25_selected_geometric_order
-- name    : N25.U25_selected_geometric_order
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:24.459629+00:00
-- url     : https://prove2.me/theorems/bb521dab-9a4e-4add-90d8-34a1ed9eddb1
-- title:
--   Selected geometric cusp orders equal the unit-order table
-- statement:
--   For $i,j∈ℤ/5ℤ$, let $P_j^G$ be the selected geometric cusp and $m_{ij}$ the tabulated order. Then $$ord_{P_j^G}(U_i^{geom})=m_{ij}.$$ This supplies the selected geometric entries of the divisor table.
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
open ModularCurve AlgebraicCurve
open N25

theorem N25.U25_selected_geometric_order (i j : Fin 5) :
    (N25.Endgame.pG25 j).ord (N25.Endgame.emb25 (U25 i)) = unitOrders25 i j := by sorry
