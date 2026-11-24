-- Prove2me | Theorems.Thm_GlobalTheory_ArchChar_abs_coord_le
-- name    : GlobalTheory.ArchChar.abs_coord_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T05:25:32.366541+00:00
-- url     : https://prove2.me/theorems/e9e81974-1b1c-46bf-94b8-e6b12f81ec63
-- title:
--   Arch Char: abs coord le
-- statement:
--   The Arch Char construction uses the abs coord le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CharConstOnTranslatesTrivial.lean#L62-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/SatakeParameters/CharConstOnTranslatesTrivial.lean#L62-L65

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

theorem GlobalTheory.ArchChar.abs_coord_le {a y : ι → ℝ} {C : ℝ} (h : ‖a - y‖ ≤ C) (i : ι) : |a i - y i| ≤ C := by sorry
