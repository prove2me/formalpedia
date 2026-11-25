-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_thetaT_eq_longestWeyl
-- name    : GroundTheory.Automorphic.ContragredientTranspose.thetaT_eq_longestWeyl
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:17:17.415825+00:00
-- url     : https://prove2.me/theorems/97ede629-04e0-5a1b-8d5a-c312884c8e43
-- title:
--   Contragredient Transpose: theta T eq longest Weyl
-- statement:
--   The Contragredient Transpose construction uses the theta T eq longest Weyl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose.lean#L67-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose.lean#L67-L75

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_GelfandKazhdan
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose_Character
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerLocal
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_MapThetaTInvariant
import Definitions.Def_GroundTheory_AutomorphicForms_ContragredientTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.ContragredientTranspose
open MeasureTheory Measure GroundTheory.Automorphic.Whittaker
variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}
omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem GroundTheory.Automorphic.ContragredientTranspose.thetaT_eq_longestWeyl (g : GL (Fin n) F) :
    thetaT g = longestWeyl * theta g * longestWeyl := by sorry
