-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isUnramified_iff
-- name    : GroundTheory.LocalField.isUnramified_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:18:21.237288+00:00
-- url     : https://prove2.me/theorems/3d4a2b29-80e4-41b0-9be7-748ffb891fb2
-- title:
--   Local Field: is Unramified iff
-- statement:
--   The Local Field construction uses the is Unramified iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedDefs.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedDefs.lean#L21-L22

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
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

theorem GroundTheory.LocalField.isUnramified_iff : IsUnramified K L ↔ ramificationIndex K L = 1 := by sorry
