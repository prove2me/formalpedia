-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_ip_sum_left
-- name    : GlobalTheory.GramCount.ip_sum_left
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T13:58:52.985022+00:00
-- url     : https://prove2.me/theorems/67e0a143-d049-4b23-9791-8e3de8b17231
-- title:
--   Gram Count: ip sum left
-- statement:
--   The Gram Count construction uses the ip sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimOfIsUnitDet.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimOfIsUnitDet.lean#L47-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.GramCount
variable {A : Type} [CommRing A]
variable (c : A →+* A) {n : ℕ}

theorem GlobalTheory.GramCount.ip_sum_left {ι : Type} (s : Finset ι) (x : ι → Fin n → A) (y : Fin n → A) :
    ip c (∑ a ∈ s, x a) y = ∑ a ∈ s, ip c (x a) y := by sorry
