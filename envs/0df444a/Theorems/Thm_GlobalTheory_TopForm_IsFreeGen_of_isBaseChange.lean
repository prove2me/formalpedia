-- Prove2me | Theorems.Thm_GlobalTheory_TopForm_IsFreeGen_of_isBaseChange
-- name    : GlobalTheory.TopForm.IsFreeGen.of_isBaseChange
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:26.662079+00:00
-- url     : https://prove2.me/theorems/9731a404-2664-438c-bcae-cb42706ec4dc
-- title:
--   Is Free Gen: of is Base Change
-- statement:
--   The Is Free Gen construction uses the of is Base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L111-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L111-L121

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
variable {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
  [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]

theorem GlobalTheory.TopForm.IsFreeGen.of_isBaseChange {φ : M →ₗ[A] N} (hφ : IsBaseChange B φ) {ω : M}
    (h : IsFreeGen A ω) : IsFreeGen B (φ ω) := by sorry
