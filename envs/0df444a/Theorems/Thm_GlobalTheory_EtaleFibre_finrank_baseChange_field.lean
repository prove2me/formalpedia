-- Prove2me | Theorems.Thm_GlobalTheory_EtaleFibre_finrank_baseChange_field
-- name    : GlobalTheory.EtaleFibre.finrank_baseChange_field
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:59:13.779869+00:00
-- url     : https://prove2.me/theorems/52fede48-4489-42df-b77e-b18b33deadd9
-- title:
--   Etale Fibre: finrank base Change field
-- statement:
--   The Etale Fibre construction uses the finrank base Change field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EtaleFibreEmbeddingsCard.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EtaleFibreEmbeddingsCard.lean#L7-L13

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

theorem GlobalTheory.EtaleFibre.finrank_baseChange_field (A M L : Type*) [CommRing A] [IsDomain A] [AddCommGroup M]
    [Module A M] [Module.Finite A M] [Module.Flat A M] [Field L] [Algebra A L] :
    Module.finrank L (L ⊗[A] M) = Module.finrank A M := by sorry
