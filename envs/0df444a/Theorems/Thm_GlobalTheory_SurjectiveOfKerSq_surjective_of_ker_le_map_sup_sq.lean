-- Prove2me | Theorems.Thm_GlobalTheory_SurjectiveOfKerSq_surjective_of_ker_le_map_sup_sq
-- name    : GlobalTheory.SurjectiveOfKerSq.surjective_of_ker_le_map_sup_sq
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:23:18.4689+00:00
-- url     : https://prove2.me/theorems/3d38ec89-349b-4f88-925f-463ca724dcb5
-- title:
--   Surjective Of Ker Sq: surjective of ker le map sup sq
-- statement:
--   The Surjective Of Ker Sq construction uses the surjective of ker le map sup sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SurjectiveOfKerLeMapSupSq.lean#L21-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/SurjectiveOfKerLeMapSupSq.lean#L21-L80

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

theorem GlobalTheory.SurjectiveOfKerSq.surjective_of_ker_le_map_sup_sq {V : Type} [CommRing V] {A B : Type} [CommRing A]
    [Algebra V A] [CommRing B] [Algebra V B] (f : A →ₐ[V] B) (aug : B →ₐ[V] V) (m : ℕ)
    (hnil : RingHom.ker aug ^ (m + 1) = ⊥) (J : Ideal A)
    (h1 : Ideal.map f J ≤ RingHom.ker aug)
    (h2 : RingHom.ker aug ≤ Ideal.map f J ⊔ RingHom.ker aug ^ 2) :
    Function.Surjective f := by sorry
