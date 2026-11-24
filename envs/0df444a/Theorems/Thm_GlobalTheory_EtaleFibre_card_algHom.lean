-- Prove2me | Theorems.Thm_GlobalTheory_EtaleFibre_card_algHom
-- name    : GlobalTheory.EtaleFibre.card_algHom
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:59:03.919849+00:00
-- url     : https://prove2.me/theorems/e4c00ce2-5040-4362-af33-2876dc80b61f
-- title:
--   Etale Fibre: card alg Hom
-- statement:
--   The Etale Fibre construction uses the card alg Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EtaleFibreEmbeddingsCard.lean#L15-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EtaleFibreEmbeddingsCard.lean#L15-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EtaleFibreEmbeddingsCard
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory GlobalTheory.EtaleFibre

theorem GlobalTheory.EtaleFibre.card_algHom (A B L : Type*) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Module.Finite A B] [Algebra.Etale A B] [Field L] [IsSepClosed L] [Algebra A L] :
    Finite (B →ₐ[A] L) ∧ Nat.card (B →ₐ[A] L) = Module.finrank A B := by sorry
