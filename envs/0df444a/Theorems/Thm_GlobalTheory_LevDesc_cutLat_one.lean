-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_cutLat_one
-- name    : GlobalTheory.LevDesc.cutLat_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:17.408827+00:00
-- url     : https://prove2.me/theorems/84a24b9b-516a-46fc-9844-f14711b2f2b0
-- title:
--   Lev Desc: cut Lat one
-- statement:
--   The Lev Desc construction uses the cut Lat one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L170-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L170-L171

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

theorem GlobalTheory.LevDesc.cutLat_one (N : Submodule O C) : cutLat N 1 = N := by sorry
