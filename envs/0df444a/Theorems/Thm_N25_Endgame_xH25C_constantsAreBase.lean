-- Prove2me | Theorems.Thm_N25_Endgame_xH25C_constantsAreBase
-- name    : N25.Endgame.xH25C_constantsAreBase
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:16.446449+00:00
-- url     : https://prove2.me/theorems/5e74bc16-57d0-4f49-a8bd-57518802cb24
-- title:
--   The level-$25$ function field has only base-field constants
-- statement:
--   Let $K$ be a perfect field and let $F_K$ be the level-$25$ modular function field over $K$. Let $L_{F_K}(0)$ denote the Riemann--Roch space of elements of $F_K$ having no poles at any place, and identify $K$ with its image in $F_K$. Then
--
--   $$L_{F_K}(0)=K.$$
--
--   This supplies the constant-field condition required to treat $F_K$ as a function field of a curve over $K$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_ModularCurve_deg_qInftyPlaceBar
import Theorems.Thm_ModularCurve_order_jqModC
import Definitions.Def_N25_Endgame
import Theorems.Thm_ModularCurve_transcendental_jqModC
import Definitions.Def_ModularCurve_X0ModL
import Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_of_isAlgClosed
import Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_le_of_eq_coeffMap
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.xH25C_constantsAreBase
    (K : Type*) [Field K] [PerfectField K] :
    AlgebraicCurve.ConstantsAreBase K (FBase K) := by sorry
