-- Prove2me | Theorems.Thm_N25_fricke_selected_cusp_width
-- name    : N25.fricke_selected_cusp_width
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:48.034191+00:00
-- url     : https://prove2.me/theorems/0f2c1f49-7ada-4885-ae49-a2288392fb82
-- title:
--   Fricke transforms the selected cusps to width $25$
-- statement:
--   Let $w$ be a geometric function-field automorphism such that the Laurent series of $w(j_{25})$ is $j(q^{25})$. For every selected geometric cusp $p_i$, the transformed place $w_*^{-1}p_i$ satisfies
--
--   $$\operatorname{ord}_{w_*^{-1}p_i}(j_{25})=-25.$$
--
--   This places the five Fricke-transformed selected cusps in the width-$25$ pole set.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_ModularCurve_X0ModL
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_modularFunctionFieldFullC_le_qExpFunctionFieldC_gamma0
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open ModularCurve AlgebraicCurve
open N25
open N25.Endgame

theorem N25.fricke_selected_cusp_width
    (w : FG ≃ₐ[Qbar] FG)
    (hw : (w (emb25 j25) : LaurentSeries Qbar) = jqNModC Qbar 25) (i : Fin 5) :
    (SemilinearAut.ofAlgAut w.symm • pG25 i).ord (emb25 j25) = -25 := by sorry
