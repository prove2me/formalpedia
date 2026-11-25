-- Prove2me | Theorems.Thm_GroundTheory_LocalField_valuativeExtension_of_isScalarTower
-- name    : GroundTheory.LocalField.valuativeExtension_of_isScalarTower
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:00:48.66689+00:00
-- url     : https://prove2.me/theorems/1441f488-36b1-4c78-aaca-5a60e3ba17af
-- title:
--   Local Field: valuative Extension of is Scalar Tower
-- statement:
--   The Local Field construction uses the valuative Extension of is Scalar Tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Uniqueness.lean#L128-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Uniqueness.lean#L128-L130

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
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
open ValuativeRel Topology Filter
variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M]

theorem GroundTheory.LocalField.valuativeExtension_of_isScalarTower [Algebra L M] [IsScalarTower K L M] :
    ValuativeExtension L M := by sorry
