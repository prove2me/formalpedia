-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HostConjugateIdeal_Level_Dvd_trans
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Level.Dvd.trans
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:37:00.161037+00:00
-- url     : https://prove2.me/theorems/038126fd-7861-4482-8c8b-d189b90ff72e
-- title:
--   Dvd: trans
-- statement:
--   The Dvd construction uses the trans property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/HostConjugateIdeal.lean#L195-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/CMModuli/HostConjugateIdeal.lean#L195-L196

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_CMModuli_HostConjugateIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal
variable (E : Type) [Field E] [NumberField E] [IsCMField E]
variable {E}
open GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Level
variable {H : Host E}

theorem GlobalTheory.IndefiniteRowSideFullHecke.HostConjugateIdeal.Level.Dvd.trans {L L₂ L₃ : Level H} (h : L.Dvd L₂) (h' : L₂.Dvd L₃) : L.Dvd L₃ := by sorry
