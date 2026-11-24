-- Prove2me | Theorems.Thm_GlobalTheory_det_ne_zero_of_generic_linear_forms_vanish
-- name    : GlobalTheory.det_ne_zero_of_generic_linear_forms_vanish
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:15:56.87229+00:00
-- url     : https://prove2.me/theorems/918b255d-44f2-432f-bcdc-742f0210e312
-- title:
--   Global Theory: det ne zero of generic linear forms vanish
-- statement:
--   The Global Theory construction uses the det ne zero of generic linear forms vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/DetNeZeroOfGenericLinearFormsVanish.lean#L8-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/DetNeZeroOfGenericLinearFormsVanish.lean#L8-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_InjectiveOfInjectiveCompAevalOfTrdegLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_DetNeZeroOfGenericLinearFormsVanish
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open MvPolynomial

theorem GlobalTheory.det_ne_zero_of_generic_linear_forms_vanish :
    ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (F : IntermediateField k K) (g N : ℕ)
    (T : Fin g × Fin N → K) (e : Fin N → K) (D : Fin g → Fin N → K),
    AlgebraicIndependent k T → Algebra.trdeg k F ≤ g → (∀ j, e j ∈ F) → (∀ a j, D a j ∈ F) →
    (∃ j, e j ≠ 0) →
    (∃ c : Fin g → Fin N → K, (∀ i, ∑ j, c i j * e j = 0) ∧
      (Matrix.of fun i a => ∑ j, c i j * D a j).det ≠ 0) →
    (∀ i, ∑ j, T (i, j) * e j = 0) → (Matrix.of fun i a => ∑ j, T (i, j) * D a j).det ≠ 0 := by sorry
