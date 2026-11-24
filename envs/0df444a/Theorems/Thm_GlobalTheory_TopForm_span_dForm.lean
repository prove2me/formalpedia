-- Prove2me | Theorems.Thm_GlobalTheory_TopForm_span_dForm
-- name    : GlobalTheory.TopForm.span_dForm
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:08:41.215827+00:00
-- url     : https://prove2.me/theorems/c1e469cb-82b9-4198-8851-d7fa9927d027
-- title:
--   Top Form: span d Form
-- statement:
--   The Top Form construction uses the span d Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L183-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L183-L191

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_AlternatingMapSumSmulEqDetSmul
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsAlgHomOfIsBaseChange
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.TopForm
variable {k A B C : Type*} [CommRing k] [CommRing A] [CommRing B] [CommRing C]
variable {D : ℕ}
variable {α : k →+* A} {β : k →+* B} {γ : k →+* C}

theorem GlobalTheory.TopForm.span_dForm (α : k →+* A) (D : ℕ) :
    Submodule.span A (Set.range (dForm α (D := D))) = ⊤ := by sorry
