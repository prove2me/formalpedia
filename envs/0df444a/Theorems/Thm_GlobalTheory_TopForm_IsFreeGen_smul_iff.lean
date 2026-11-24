-- Prove2me | Theorems.Thm_GlobalTheory_TopForm_IsFreeGen_smul_iff
-- name    : GlobalTheory.TopForm.IsFreeGen.smul_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:07:28.109996+00:00
-- url     : https://prove2.me/theorems/77f5e4dc-5f86-453f-ab22-80789bac2159
-- title:
--   Is Free Gen: smul iff
-- statement:
--   The Is Free Gen construction uses the smul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L156-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L156-L160

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
variable {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M] {ω : M}

theorem GlobalTheory.TopForm.IsFreeGen.smul_iff (h : IsFreeGen A ω) {a : A} : IsFreeGen A (a • ω) ↔ IsUnit a := by sorry
