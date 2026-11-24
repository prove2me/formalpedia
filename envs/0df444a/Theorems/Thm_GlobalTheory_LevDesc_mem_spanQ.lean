-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_mem_spanQ
-- name    : GlobalTheory.LevDesc.mem_spanQ
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:03:12.092161+00:00
-- url     : https://prove2.me/theorems/ec8dcb63-1e1f-4520-ba97-56b343351494
-- title:
--   Lev Desc: mem span Q
-- statement:
--   The Lev Desc construction uses the mem span Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L155-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L155-L156

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
omit [Algebra O K] [IsScalarTower O K C]

theorem GlobalTheory.LevDesc.mem_spanQ {N : Submodule O C} {F : C} (hF : F ∈ N) : (F : R) ∈ spanQ N := by sorry
