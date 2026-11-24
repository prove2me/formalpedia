-- Prove2me | Theorems.Thm_GlobalTheory_CapelliTop_list_ite
-- name    : GlobalTheory.CapelliTop.list_ite
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:07:14.917+00:00
-- url     : https://prove2.me/theorems/d563019e-c046-4f07-bf44-035773e10ad0
-- title:
--   Capelli Top: list ite
-- statement:
--   The Capelli Top construction uses the list ite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/QdetTopThreeOrders.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/QdetTopThreeOrders.lean#L31-L35

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

theorem GlobalTheory.CapelliTop.list_ite {ι : Type} (p : ι → Prop) [DecidablePred p] (e : ι → A) (l : List ι) :
    (l.map fun k => if p k then e k else 1).prod = ((l.filter fun k => decide (p k)).map e).prod := by sorry
