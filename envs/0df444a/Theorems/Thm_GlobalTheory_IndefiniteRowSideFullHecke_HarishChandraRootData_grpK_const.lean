-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HarishChandraRootData_grpK_const
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData.grpK_const
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T02:49:43.252869+00:00
-- url     : https://prove2.me/theorems/e990a41f-ca23-5a14-b204-465384a41bc8
-- title:
--   Harish Chandra Root Data: grp K const
-- statement:
--   The Harish Chandra Root Data construction uses the grp K const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/HarishChandraParameters.lean#L117-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/HarishChandraParameters.lean#L117-L120

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_HarishChandraParameters
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData
variable {n : ℕ}

theorem GlobalTheory.IndefiniteRowSideFullHecke.HarishChandraRootData.grpK_const (k : ℕ) : grpK (fun _ : Fin k => true) =
    (Matrix.unitaryGroup (Fin k) ℂ : Set (Matrix (Fin k) (Fin k) ℂ)) := by sorry
