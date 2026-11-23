-- Prove2me | Theorems.Thm_GlobalTheory_QFam_QConj_const
-- name    : GlobalTheory.QFam.QConj.const
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:15:04.453186+00:00
-- url     : https://prove2.me/theorems/4fa1b25f-b418-4c33-ad59-29bd7bbae7b6
-- title:
--   QConj: const
-- statement:
--   The QConj construction uses the const property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QExpansionsCoeffwiseConjugateRingClosure.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QExpansionsCoeffwiseConjugateRingClosure.lean#L12-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelLinearOperations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelMulOfPosLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionsCoeffwiseConjugateRingClosure
import Theorems.Thm_GlobalTheory_QFam_HasQ_const

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

theorem GlobalTheory.QFam.QConj.const (g : ℂ ≃+* ℂ) (N : ℕ) (c : ℂ) : QConj g N (fun _ => c) fun _ => g c := by sorry
