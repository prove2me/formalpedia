-- Prove2me | Theorems.Thm_GlobalTheory_NB_cHyp_iff
-- name    : GlobalTheory.NB.cHyp_iff
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:15:31.006238+00:00
-- url     : https://prove2.me/theorems/23bfedbf-fe56-4d0c-a705-1f7fbe00a162
-- title:
--   NB: c Hyp iff
-- statement:
--   The NB construction uses the c Hyp iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/OfKillsOne.lean#L189-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/OfKillsOne.lean#L189-L195

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

theorem GlobalTheory.NB.cHyp_iff [NeZero n] {b : ZMod n → ℕ} {Sn η m h : ℕ} :
    CHyp F b Sn η m h ↔ CSet F b Sn η m h ∧ (∀ i, ∃ a : ℕ, F.Kills i ((l : O⟦X⟧) ^ a)) ∧
      ∀ i, F.Kills i (R.E ^ aC l (h + η)) := by sorry
