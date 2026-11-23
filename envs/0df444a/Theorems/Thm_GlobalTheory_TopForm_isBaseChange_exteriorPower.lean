-- Prove2me | Theorems.Thm_GlobalTheory_TopForm_isBaseChange_exteriorPower
-- name    : GlobalTheory.TopForm.isBaseChange_exteriorPower
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:03:23.375237+00:00
-- url     : https://prove2.me/theorems/6d87aec1-45b7-482a-b9f4-be04bcd1d9b6
-- title:
--   Top Form: is Base Change exterior Power
-- statement:
--   The Top Form construction uses the is Base Change exterior Power property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L58-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsAlgHomOfIsBaseChange.lean#L58-L106

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

theorem GlobalTheory.TopForm.isBaseChange_exteriorPower {φ : M →ₗ[A] N} (hφ : IsBaseChange B φ) (D : ℕ) :
    IsBaseChange B (exteriorPowerMapOver B D φ) := by sorry
