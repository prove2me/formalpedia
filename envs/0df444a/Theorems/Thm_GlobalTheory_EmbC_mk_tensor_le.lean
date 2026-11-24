-- Prove2me | Theorems.Thm_GlobalTheory_EmbC_mk_tensor_le
-- name    : GlobalTheory.EmbC.mk_tensor_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:58:17.070804+00:00
-- url     : https://prove2.me/theorems/9ec4f873-fa52-43c1-85e7-65b42d80dbda
-- title:
--   Emb C: mk tensor le
-- statement:
--   The Emb C construction uses the mk tensor le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MkTensorLe.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/MkTensorLe.lean#L7-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_MkTensorLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EmbC
open Cardinal TensorProduct

theorem GlobalTheory.EmbC.mk_tensor_le (R A B : Type) [CommRing R] [AddCommGroup A] [AddCommGroup B] [Module R A] [Module R B]
    (hA : #A ≤ 𝔠) (hB : #B ≤ 𝔠) : #(A ⊗[R] B) ≤ 𝔠 := by sorry
