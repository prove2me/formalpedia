-- Prove2me | Theorems.Thm_GlobalTheory_T_bialgHomCotangentPullback_injective_of_sq
-- name    : GlobalTheory.T.bialgHomCotangentPullback_injective_of_sq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:11:40.345711+00:00
-- url     : https://prove2.me/theorems/1c4816d8-aee8-4ea7-acc3-37df8d04740c
-- title:
--   T: bialg Hom Cotangent Pullback injective of sq
-- statement:
--   The T construction uses the bialg Hom Cotangent Pullback injective of sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BialgHomCotangentPullbackInjectiveOfSqStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BialgHomCotangentPullbackInjectiveOfSqStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BialgHomCotangentPullbackInjectiveOfSq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_RigOfOmegaInjectiveOfEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BialgHomCotangentPullbackInjectiveOfSqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.bialgHomCotangentPullback_injective_of_sq : ∀ (R C A : Type) [CommRing R] [CommRing C] [CommRing A] [Bialgebra R C] [Bialgebra R A] (f : C →ₐc[R] A), (∀ b : C, f b ∈ RingHom.ker (Bialgebra.counitAlgHom R A) ^ 2 → b ∈ RingHom.ker (Bialgebra.counitAlgHom R C) ^ 2) → Function.Injective (GlobalTheory.PDiv.cotMap f) := by sorry
