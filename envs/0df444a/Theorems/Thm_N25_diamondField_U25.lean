-- Prove2me | Theorems.Thm_N25_diamondField_U25
-- name    : N25.diamondField_U25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:52:16.377352+00:00
-- url     : https://prove2.me/theorems/5c52bbdb-a5fa-4eb2-973b-26466e738b0a
-- title:
--   The label-$13$ diamond permutes the five modular units with signs
-- statement:
--   Let $U_i$ for $i\in\mathbb Z/5\mathbb Z$ be the five rational modular units, embedded in the geometric function field, and let $\delta_{13}$ be the label-$13$ diamond automorphism. For the sign vector $\varepsilon=(-1,-1,1,-1,-1)$,
--
--   $$\delta_{13}(U_i)=\varepsilon_iU_{i-1}.$$
--
--   This gives the explicit cyclic diamond action on the unit generators.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_N25_Endgame
import Definitions.Def_N25_UnitAnalytic
import Theorems.Thm_ModularCurve_qExpansion_discriminant_eq_map_X_mul_dedekindEtaUnit
import Definitions.Def_N25_UnitSeries
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_exists_monoidHom_gamma0_algEquiv_qExpFunctionFieldC_gammaH_of_charZero
import Theorems.Thm_ModularCurve_diamondAutHBar_apply_coeffEmb_eq_coeffEmb_ringAut_apply

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open ModularCurve CongruenceSubgroup
open scoped MatrixGroups ModularForm
open N25

theorem N25.diamondField_U25 (i : Fin 5) :
    let ε : Fin 5 → N25.Endgame.FG := ![-1,-1,1,-1,-1]
    diamondAutHBar 25 N25.H25 (ZMod.unitOfCoprime 13 (by decide))
        (N25.Endgame.emb25 (U25 i)) =
      ε i * N25.Endgame.emb25 (U25 (i-1)) := by sorry
