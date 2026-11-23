-- Prove2me | Theorems.Thm_GlobalTheory_HermForm_Nondegenerate_unimodular
-- name    : GlobalTheory.HermForm.Nondegenerate.unimodular
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:17.264983+00:00
-- url     : https://prove2.me/theorems/ff7ced93-1aa8-4882-a83d-effbc7ca36b6
-- title:
--   Nondegenerate: unimodular
-- statement:
--   The Nondegenerate construction uses the unimodular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L358-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Foundations/MemUnitaryGroupIffIsIsometry.lean#L358-L368

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

theorem GlobalTheory.HermForm.Nondegenerate.unimodular (H : h.Nondegenerate) : h.Unimodular := by sorry
