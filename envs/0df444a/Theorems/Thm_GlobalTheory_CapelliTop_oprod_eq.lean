-- Prove2me | Theorems.Thm_GlobalTheory_CapelliTop_oprod_eq
-- name    : GlobalTheory.CapelliTop.oprod_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:55:44.732813+00:00
-- url     : https://prove2.me/theorems/c48ea0a3-cc9a-4aa7-a798-2451d33d98d2
-- title:
--   Capelli Top: oprod eq
-- statement:
--   The Capelli Top construction uses the oprod eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/QdetTopThreeOrders.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/QdetTopThreeOrders.lean#L37-L43

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_QdetTopThreeOrders
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CapelliTop
variable {A : Type} [Ring A] {n : ℕ}

theorem GlobalTheory.CapelliTop.oprod_eq (S : Finset (Fin n)) (e : Fin n → A) (l : List (Fin n)) (hl : l.Pairwise (· < ·))
    (h : ∀ k, k ∈ l ↔ k ∈ S) : oprod S e = (l.map e).prod := by sorry
