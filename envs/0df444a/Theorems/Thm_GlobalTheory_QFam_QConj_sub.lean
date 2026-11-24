-- Prove2me | Theorems.Thm_GlobalTheory_QFam_QConj_sub
-- name    : GlobalTheory.QFam.QConj.sub
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:00:13.398339+00:00
-- url     : https://prove2.me/theorems/a43fe6cf-702d-4e0c-a7e5-20bccf3c2c52
-- title:
--   QConj: sub
-- statement:
--   The QConj construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QExpansionsCoeffwiseConjugateRingClosure.lean#L27-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QExpansionsCoeffwiseConjugateRingClosure.lean#L27-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelLinearOperations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelMulOfPosLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionsCoeffwiseConjugateRingClosure
import Theorems.Thm_GlobalTheory_QFam_HasQ_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory GlobalTheory.QFam
variable {g : ℂ ≃+* ℂ} {N : ℕ}

theorem GlobalTheory.QFam.QConj.sub {f f' h h' : ℍ → ℂ} (hf : QConj g N f f') (hh : QConj g N h h') :
    QConj g N (fun τ => f τ - h τ) fun τ => f' τ - h' τ := by sorry
