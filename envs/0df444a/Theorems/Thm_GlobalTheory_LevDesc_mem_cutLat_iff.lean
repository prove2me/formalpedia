-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_mem_cutLat_iff
-- name    : GlobalTheory.LevDesc.mem_cutLat_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:55:58.872541+00:00
-- url     : https://prove2.me/theorems/ba626bf3-4037-4cd0-b8e3-9a8fff6fb594
-- title:
--   Lev Desc: mem cut Lat iff
-- statement:
--   The Lev Desc construction uses the mem cut Lat iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L163-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L163-L168

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

theorem GlobalTheory.LevDesc.mem_cutLat_iff {N : Submodule O C} {T : Module.End K R} (hT : IsIdempotentElem T) {F : C} :
    F ∈ cutLat N T ↔ F ∈ N ∧ T F = F := by sorry
