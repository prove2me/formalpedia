-- Prove2me | Theorems.Thm_GlobalTheory_CapelliTop_subdet_single
-- name    : GlobalTheory.CapelliTop.subdet_single
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:08:41.655846+00:00
-- url     : https://prove2.me/theorems/99a43efb-c706-4903-9456-bfbe4e7d8cf0
-- title:
--   Capelli Top: subdet single
-- statement:
--   The Capelli Top construction uses the subdet single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/QdetTopThreeOrders.lean#L80-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/QdetTopThreeOrders.lean#L80-L95

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

theorem GlobalTheory.CapelliTop.subdet_single (E : Fin n → Fin n → A) (i : Fin n) : subdet E {i} = E i i := by sorry
