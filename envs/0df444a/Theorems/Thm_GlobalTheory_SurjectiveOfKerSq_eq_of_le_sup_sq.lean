-- Prove2me | Theorems.Thm_GlobalTheory_SurjectiveOfKerSq_eq_of_le_sup_sq
-- name    : GlobalTheory.SurjectiveOfKerSq.eq_of_le_sup_sq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T20:23:21.389798+00:00
-- url     : https://prove2.me/theorems/8bce3761-fd71-4505-8011-397c0867fbcc
-- title:
--   Surjective Of Ker Sq: eq of le sup sq
-- statement:
--   The Surjective Of Ker Sq construction uses the eq of le sup sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SurjectiveOfKerLeMapSupSq.lean#L5-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SurjectiveOfKerLeMapSupSq.lean#L5-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_SurjectiveOfKerLeMapSupSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.SurjectiveOfKerSq

theorem GlobalTheory.SurjectiveOfKerSq.eq_of_le_sup_sq {B : Type} [CommRing B] (I K : Ideal B) (m : ℕ)
    (hnil : I ^ (m + 1) = ⊥) (h1 : K ≤ I) (h2 : I ≤ K ⊔ I ^ 2) : I = K := by sorry
