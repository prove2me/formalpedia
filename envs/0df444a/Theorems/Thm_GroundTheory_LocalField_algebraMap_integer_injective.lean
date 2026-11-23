-- Prove2me | Theorems.Thm_GroundTheory_LocalField_algebraMap_integer_injective
-- name    : GroundTheory.LocalField.algebraMap_integer_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:59:09.38556+00:00
-- url     : https://prove2.me/theorems/ecb7339d-de6d-4882-888a-afe1bb27d692
-- title:
--   Local Field: algebra Map integer injective
-- statement:
--   The Local Field construction uses the algebra Map integer injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Interface.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Interface.lean#L24-L25

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
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
variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]

theorem GroundTheory.LocalField.algebraMap_integer_injective : Function.Injective (algebraMap 𝒪[K] 𝒪[L]) := by sorry
