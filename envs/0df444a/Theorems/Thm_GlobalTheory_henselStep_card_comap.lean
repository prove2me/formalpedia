-- Prove2me | Theorems.Thm_GlobalTheory_henselStep_card_comap
-- name    : GlobalTheory.henselStep_card_comap
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T07:46:41.101274+00:00
-- url     : https://prove2.me/theorems/504c53df-d4a9-454b-bb04-a41e0396e932
-- title:
--   Global Theory: hensel Step card comap
-- statement:
--   The Global Theory construction uses the hensel Step card comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HenselStepCardComap.lean#L8-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/HenselStepCardComap.lean#L8-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_PrimOfIsUnitDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_HenselStepCardComap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.GramCount
open scoped Classical
open GlobalTheory

theorem GlobalTheory.henselStep_card_comap {W T : Type} [AddCommGroup W] [AddCommGroup T]
    (T1 T2 : AddSubgroup T) (h21 : T2 ≤ T1) (d : W →+ T) (hd1 : ∀ w, d w ∈ T1)
    (hd2 : ∀ t ∈ T1, ∃ w, d w - t ∈ T2) :
    Nat.card (T2.comap d) * Nat.card T1 = Nat.card W * Nat.card T2 := by sorry
