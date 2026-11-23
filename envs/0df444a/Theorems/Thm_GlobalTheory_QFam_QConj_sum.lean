-- Prove2me | Theorems.Thm_GlobalTheory_QFam_QConj_sum
-- name    : GlobalTheory.QFam.QConj.sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:28:37.728622+00:00
-- url     : https://prove2.me/theorems/1985ef90-3413-43ac-8aa0-8e3a7aeffc03
-- title:
--   QConj: sum
-- statement:
--   The QConj construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QExpansionsCoeffwiseConjugateRingClosure.lean#L58-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QExpansionsCoeffwiseConjugateRingClosure.lean#L58-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HasQIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelLinearOperations
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasQExpansionOfLevelMulOfPosLevel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QExpansionsCoeffwiseConjugateRingClosure
import Theorems.Thm_GlobalTheory_QFam_HasQ_sum

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

theorem GlobalTheory.QFam.QConj.sum {κ : Type} (s : Finset κ) {f f' : κ → ℍ → ℂ}
    (h : ∀ k ∈ s, QConj g N (f k) (f' k)) :
    QConj g N (fun τ => ∑ k ∈ s, f k τ) fun τ => ∑ k ∈ s, f' k τ := by sorry
