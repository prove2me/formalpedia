-- Prove2me | Theorems.Thm_GlobalTheory_NB_Hom_Kills_of_dvd
-- name    : GlobalTheory.NB.Hom.Kills.of_dvd
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:10:12.718304+00:00
-- url     : https://prove2.me/theorems/97e4be7b-a4d0-401a-8138-515178a354ab
-- title:
--   Kills: of dvd
-- statement:
--   The Kills construction uses the of dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/OfKillsOne.lean#L171-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/OfKillsOne.lean#L171-L176

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

theorem GlobalTheory.NB.Hom.Kills.of_dvd {i : ZMod n} {f g : O⟦X⟧} (h : F.Kills i f) (hfg : f ∣ g) :
    F.Kills i g := by sorry
