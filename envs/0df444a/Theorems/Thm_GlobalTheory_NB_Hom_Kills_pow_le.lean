-- Prove2me | Theorems.Thm_GlobalTheory_NB_Hom_Kills_pow_le
-- name    : GlobalTheory.NB.Hom.Kills.pow_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:16:23.284085+00:00
-- url     : https://prove2.me/theorems/af93c172-38eb-5646-a223-5da09e2acfb0
-- title:
--   Kills: pow le
-- statement:
--   The Kills construction uses the pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/OfKillsOne.lean#L180-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/OfKillsOne.lean#L180-L181

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
omit [IsDomain O]

theorem GlobalTheory.NB.Hom.Kills.pow_le {i : ZMod n} {f : O⟦X⟧} {a a' : ℕ} (h : F.Kills i (f ^ a)) (ha : a ≤ a') :
    F.Kills i (f ^ a') := by sorry
