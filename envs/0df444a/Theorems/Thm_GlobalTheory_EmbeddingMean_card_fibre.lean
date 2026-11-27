-- Prove2me | Theorems.Thm_GlobalTheory_EmbeddingMean_card_fibre
-- name    : GlobalTheory.EmbeddingMean.card_fibre
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:19:16.411967+00:00
-- url     : https://prove2.me/theorems/cb903cf8-a946-5f35-a63c-5f873c0f89ee
-- title:
--   Embedding Mean: card fibre
-- statement:
--   The Embedding Mean construction uses the card fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExtendAndMean.lean#L5-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExtendAndMean.lean#L5-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExtendAndMean
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EmbeddingMean

theorem GlobalTheory.EmbeddingMean.card_fibre {K A B C : Type} [Field K] [Field A] [Field B] [Field C] [CharZero K]
    [Algebra K A] [Algebra K B] [Algebra K C] [Algebra A B] [IsScalarTower K A B]
    [FiniteDimensional K A] [FiniteDimensional K B] [IsAlgClosed C] [DecidableEq (A →ₐ[K] C)]
    (f : A →ₐ[K] C) :
    (Finset.univ.filter (fun g : B →ₐ[K] C => g.comp (IsScalarTower.toAlgHom K A B) = f)).card
      = Module.finrank A B := by sorry
