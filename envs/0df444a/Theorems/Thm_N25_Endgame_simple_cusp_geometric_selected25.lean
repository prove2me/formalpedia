-- Prove2me | Theorems.Thm_N25_Endgame_simple_cusp_geometric_selected25
-- name    : N25.Endgame.simple_cusp_geometric_selected25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:39.806418+00:00
-- url     : https://prove2.me/theorems/1e3a8b53-f289-4ecc-a254-ff38764eddb4
-- title:
--   Every simple pole of the $j$-map is a selected cusp
-- statement:
--   Let $F_{\mathrm{geom}}$ be the geometric function field of the level-$25$ modular curve, let $j$ be the embedded modular $j$-function, and let $p_0,\ldots,p_4$ be the five selected geometric cusps. If $P$ is a place of $F_{\mathrm{geom}}$ at which $j$ has a simple pole, then
--
--   $$\operatorname{ord}_P(j)=-1\quad\Longrightarrow\quad \exists i\in\{0,1,2,3,4\},\ P=p_i.$$
--
--   This shows that the selected cusp list exhausts the simple poles needed for the modular-unit and divisor arguments.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_N25
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension
import Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC
import Theorems.Thm_ModularCurve_exists_ringHom_place_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_ord_eq_neg_width_of_order_eq_mul_ord_of_qExpansion_slash
import Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_gammaH_eq_index
import Theorems.Thm_ModularCurve_exists_tendsto_realizeOf_mul_exp_of_not_mem_toValuationSubring

set_option autoImplicit false
open ModularCurve AlgebraicCurve
open N25
open N25.Endgame

theorem N25.Endgame.simple_cusp_geometric_selected25 (P : GPlace)
    (hP : P.ord (emb25 j25) = -1) : ∃ i : Fin 5, P = pG25 i := by sorry
