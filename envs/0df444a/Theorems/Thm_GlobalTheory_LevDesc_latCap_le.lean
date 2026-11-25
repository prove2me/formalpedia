-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_latCap_le
-- name    : GlobalTheory.LevDesc.latCap_le
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:13:35.951297+00:00
-- url     : https://prove2.me/theorems/1e4dea14-a2eb-4d8e-afa0-b3401d8eb8c5
-- title:
--   Lev Desc: lat Cap le
-- statement:
--   The Lev Desc construction uses the lat Cap le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L149-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L149-L149

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

theorem GlobalTheory.LevDesc.latCap_le (L : Submodule O C) (W : Submodule K R) : latCap L W ≤ L := by sorry
