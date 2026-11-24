-- Prove2me | Theorems.Thm_GlobalTheory_TopForm_IsFreeGen_repr_smul
-- name    : GlobalTheory.TopForm.IsFreeGen.repr_smul
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:07:55.367416+00:00
-- url     : https://prove2.me/theorems/20c5aa79-dd3b-4fb6-ba4c-14e96d165cfb
-- title:
--   Is Free Gen: repr smul
-- statement:
--   The Is Free Gen construction uses the repr smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L146-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L146-L147

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

theorem GlobalTheory.TopForm.IsFreeGen.repr_smul (h : IsFreeGen A ω) (x : M) : h.repr x • ω = x := by sorry
