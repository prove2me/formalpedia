-- Prove2me | Theorems.Thm_GlobalTheory_HermForm_unimodular_iff_nondegenerate
-- name    : GlobalTheory.HermForm.unimodular_iff_nondegenerate
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:04.19466+00:00
-- url     : https://prove2.me/theorems/f5c984e9-e199-50a9-91d1-1ea59055391a
-- title:
--   Herm Form: unimodular iff nondegenerate
-- statement:
--   The Herm Form construction uses the unimodular iff nondegenerate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L370-L371
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L370-L371

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemUnitaryGroupIffIsIsometry
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open NumberField
open GlobalTheory
open GlobalTheory.HermForm
variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {h : HermForm K V}

theorem GlobalTheory.HermForm.unimodular_iff_nondegenerate : h.Unimodular ↔ h.Nondegenerate := by sorry
