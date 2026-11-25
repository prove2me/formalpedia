-- Prove2me | Theorems.Thm_GroundTheory_LocalField_integerInclusion_injective
-- name    : GroundTheory.LocalField.integerInclusion_injective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:44:59.062281+00:00
-- url     : https://prove2.me/theorems/de87dfca-d93c-4ad2-8331-319297f61bb6
-- title:
--   Local Field: integer Inclusion injective
-- statement:
--   The Local Field construction uses the integer Inclusion injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalUnramifiedIntegers.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalUnramifiedIntegers.lean#L63-L67

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramifiedIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing
variable {K Ω : Type*} [Field K] [Field Ω] [ValuativeRel Ω] [Algebra K Ω]

theorem GroundTheory.LocalField.integerInclusion_injective [ValuativeRel K] [ValuativeExtension K Ω]
    {E F : IntermediateField K Ω} (h : E ≤ F) : Function.Injective (integerInclusion h) := by sorry
