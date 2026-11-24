-- Prove2me | Theorems.Thm_GlobalTheory_ArchChar_succ_pos
-- name    : GlobalTheory.ArchChar.succ_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:39.588342+00:00
-- url     : https://prove2.me/theorems/b1a02ef1-7355-42dc-8364-3830f868bde0
-- title:
--   Arch Char: succ pos
-- statement:
--   The Arch Char construction uses the succ pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CharConstOnTranslatesTrivial.lean#L70-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CharConstOnTranslatesTrivial.lean#L70-L71

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_ContinuousCharUnitsComplexStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SatakeParameters_CharConstOnTranslatesTrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.ArchChar
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.ArchChar.succ_pos (m : ℕ) : 0 < (m : ℝ) + 1 := by sorry
