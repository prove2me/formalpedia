-- Prove2me | Theorems.Thm_GlobalTheory_NB_BSet_lt_iff
-- name    : GlobalTheory.NB.BSet.lt_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:17:21.560014+00:00
-- url     : https://prove2.me/theorems/76f94926-e4ea-4d93-b945-19e9ac9b9896
-- title:
--   BSet: lt iff
-- statement:
--   The BSet construction uses the lt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/OfKillsOne.lean#L216-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/OfKillsOne.lean#L216-L221

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_RoundDown
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_OfKillsOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PowerSeries
open GlobalTheory GlobalTheory.NB
variable {l : ℕ} {O : Type} [CommRing O] [IsDomain O] {R : Fr l O} {n r₁ r : ℕ}
variable {S₁ : Sys R n r₁} {S : Sys R n r} {F : Hom S₁ S}

theorem GlobalTheory.NB.BSet.lt_iff {up : ZMod n → Bool} {sz : ZMod n → ℕ} {b w Sn η m h : ℕ}
    (H : BSet F up sz b w Sn η m h) (i : ZMod n) : sz i < b ↔ sz i ≤ w := by sorry
