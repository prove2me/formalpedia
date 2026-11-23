-- Prove2me | Theorems.Thm_GroundTheory_LocalField_exists_isNonarchimedeanLocalField_valuativeExtension
-- name    : GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T20:49:08.700566+00:00
-- url     : https://prove2.me/theorems/76d9127a-b26e-48c9-9da3-6cc4bc26aa7c
-- title:
--   Local Field: exists is Nonarchimedean Local Field valuative Extension
-- statement:
--   The Local Field construction uses the exists is Nonarchimedean Local Field valuative Extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FiniteExtension.lean#L150-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FiniteExtension.lean#L150-L155

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (L : Type*) [Field L] [Algebra K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.exists_isNonarchimedeanLocalField_valuativeExtension :
    ∃ (_ : ValuativeRel L) (_ : TopologicalSpace L),
      IsNonarchimedeanLocalField L ∧ ValuativeExtension K L := by sorry
