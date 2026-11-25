-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_coe_list_prod_transvectionGL
-- name    : GroundTheory.Automorphic.coe_list_prod_transvectionGL
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:34:34.699749+00:00
-- url     : https://prove2.me/theorems/68226c5f-ddc3-46fa-95f4-c4a96bb11cf2
-- title:
--   Automorphic: coe list prod transvection GL
-- statement:
--   The Automorphic construction uses the coe list prod transvection GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StrongApproximationSLElementary.lean#L40-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/StrongApproximationSLElementary.lean#L40-L45

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_StrongApproximationSLElementary
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GroundTheory GroundTheory.Automorphic
variable {n : Type*} [Fintype n] [DecidableEq n]
variable (n) (R : Type*) [CommRing R]
variable {n R}

theorem GroundTheory.Automorphic.coe_list_prod_transvectionGL (L : List (TransvectionStruct n R)) :
    (((L.map (transvectionGL n R)).prod : GL n R) : Matrix n n R) =
      (L.map TransvectionStruct.toMatrix).prod := by sorry
