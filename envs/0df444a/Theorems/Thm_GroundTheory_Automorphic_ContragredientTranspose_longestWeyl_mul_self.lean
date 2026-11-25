-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_ContragredientTranspose_longestWeyl_mul_self
-- name    : GroundTheory.Automorphic.ContragredientTranspose.longestWeyl_mul_self
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:24:12.604792+00:00
-- url     : https://prove2.me/theorems/8093897c-3ed9-439a-8774-2ed8763ae8ed
-- title:
--   Contragredient Transpose: longest Weyl mul self
-- statement:
--   The Contragredient Transpose construction uses the longest Weyl mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose.lean#L60-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/ContragredientTranspose.lean#L60-L63

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

theorem GroundTheory.Automorphic.ContragredientTranspose.longestWeyl_mul_self : (longestWeyl : GL (Fin n) F) * longestWeyl = 1 := by sorry
