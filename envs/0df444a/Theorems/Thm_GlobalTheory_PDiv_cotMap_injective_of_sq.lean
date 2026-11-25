-- Prove2me | Theorems.Thm_GlobalTheory_PDiv_cotMap_injective_of_sq
-- name    : GlobalTheory.PDiv.cotMap_injective_of_sq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T02:59:42.159646+00:00
-- url     : https://prove2.me/theorems/8ab801e6-a39c-4cda-8f32-101614ea44e6
-- title:
--   PDiv: cot Map injective of sq
-- statement:
--   The PDiv construction uses the cot Map injective of sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BialgHomCotangentPullbackInjectiveOfSq.lean#L8-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BialgHomCotangentPullbackInjectiveOfSq.lean#L8-L30

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BialgHomCotangentPullbackInjectiveOfSq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.PDiv

theorem GlobalTheory.PDiv.cotMap_injective_of_sq : ∀ (R C A : Type) [CommRing R] [CommRing C] [CommRing A]
    [Bialgebra R C] [Bialgebra R A] (f : C →ₐc[R] A),
    (∀ b : C, f b ∈ RingHom.ker (Bialgebra.counitAlgHom R A) ^ 2 →
      b ∈ RingHom.ker (Bialgebra.counitAlgHom R C) ^ 2) →
    Function.Injective (GlobalTheory.PDiv.cotMap f) := by sorry
