-- Prove2me | Theorems.Thm_GlobalTheory_NB_typed_iff
-- name    : GlobalTheory.NB.typed_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:10:23.816799+00:00
-- url     : https://prove2.me/theorems/dbdaab8e-00e3-44cc-be9c-40244164d905
-- title:
--   NB: typed iff
-- statement:
--   The NB construction uses the typed iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/OfKillsOne.lean#L183-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/OfKillsOne.lean#L183-L187

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

theorem GlobalTheory.NB.typed_iff {up : ZMod n → Fin R.e → Bool} {b : ZMod n → Fin R.e → ℕ} {Sn η m h : ℕ} :
    Typed F up b Sn η m h ↔
      TypedOnto F up b Sn η m h ∧ ∀ i, ∃ a : ℕ, F.Kills i ((l : O⟦X⟧) ^ a) := by sorry
