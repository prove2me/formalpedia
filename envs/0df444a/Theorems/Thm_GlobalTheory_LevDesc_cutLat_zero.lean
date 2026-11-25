-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_cutLat_zero
-- name    : GlobalTheory.LevDesc.cutLat_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:17.818177+00:00
-- url     : https://prove2.me/theorems/44e5b984-bc4b-5482-a094-0d643afd484b
-- title:
--   Lev Desc: cut Lat zero
-- statement:
--   The Lev Desc construction uses the cut Lat zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L173-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L173-L175

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevDesc
variable {G K R O : Type} [Group G] [Field K] [CommRing R] [Algebra K R] [CommRing O] [Algebra O K]
  {C : Submodule K R} [Module O C] [IsScalarTower O K C]

theorem GlobalTheory.LevDesc.cutLat_zero (N : Submodule O C) : cutLat N 0 = ⊥ := by sorry
