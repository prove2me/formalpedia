-- Prove2me | Theorems.Thm_GlobalTheory_TopForm_dForm_eq_det_smul
-- name    : GlobalTheory.TopForm.dForm_eq_det_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:47:03.213807+00:00
-- url     : https://prove2.me/theorems/43f52110-8b4e-4c0d-b9ff-32bbe4df4668
-- title:
--   Top Form: d Form eq det smul
-- statement:
--   The Top Form construction uses the d Form eq det smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L275-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L275-L278

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

theorem GlobalTheory.TopForm.dForm_eq_det_smul (f x : Fin D → A) (a : Matrix (Fin D) (Fin D) A)
    (h : ∀ i, dFun α (f i) = ∑ j, a i j • dFun α (x j)) : dForm α f = a.det • dForm α x := by sorry
