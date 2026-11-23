-- Prove2me | Theorems.Thm_GlobalTheory_TopForm_dForm_eq
-- name    : GlobalTheory.TopForm.dForm_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:02:13.409989+00:00
-- url     : https://prove2.me/theorems/b5f272a0-e577-4ff3-92c0-79fde220081b
-- title:
--   Top Form: d Form eq
-- statement:
--   The Top Form construction uses the d Form eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L178-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L178-L179

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

theorem GlobalTheory.TopForm.dForm_eq (α : k →+* A) (f : Fin D → A) :
    dForm α f = exteriorPower.ιMulti A D fun i => dFun α (f i) := by sorry
