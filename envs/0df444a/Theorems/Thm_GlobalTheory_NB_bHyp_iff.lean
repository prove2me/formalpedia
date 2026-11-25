-- Prove2me | Theorems.Thm_GlobalTheory_NB_bHyp_iff
-- name    : GlobalTheory.NB.bHyp_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:59.813481+00:00
-- url     : https://prove2.me/theorems/0b6683de-3219-4ce3-a5b5-5318ccef51eb
-- title:
--   NB: b Hyp iff
-- statement:
--   The NB construction uses the b Hyp iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/OfKillsOne.lean#L197-L204
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/OfKillsOne.lean#L197-L204

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

theorem GlobalTheory.NB.bHyp_iff [NeZero n] {up : ZMod n → Bool} {sz : ZMod n → ℕ} {b w Sn η m h : ℕ}
    {A ρ : ZMod n → ℕ} :
    BHyp F up sz b w Sn η m h A ρ ↔ BSet F up sz b w Sn η m h ∧ CutBounds F sz w Sn η h A ρ := by sorry
