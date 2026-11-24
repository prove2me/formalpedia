-- Prove2me | Theorems.Thm_GlobalTheory_GramCount_ip_sum_right
-- name    : GlobalTheory.GramCount.ip_sum_right
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T13:59:07.747385+00:00
-- url     : https://prove2.me/theorems/bae92458-c7e4-4ea6-9da2-e326afe8dea1
-- title:
--   Gram Count: ip sum right
-- statement:
--   The Gram Count construction uses the ip sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimOfIsUnitDet.lean#L53-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/PrimOfIsUnitDet.lean#L53-L57

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

theorem GlobalTheory.GramCount.ip_sum_right {ι : Type} (s : Finset ι) (x : Fin n → A) (y : ι → Fin n → A) :
    ip c x (∑ a ∈ s, y a) = ∑ a ∈ s, ip c x (y a) := by sorry
