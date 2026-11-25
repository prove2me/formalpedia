-- Prove2me | Theorems.Thm_GroundTheory_LocalField_maximalUnramified_le_fixedField
-- name    : GroundTheory.LocalField.maximalUnramified_le_fixedField
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:50:18.838399+00:00
-- url     : https://prove2.me/theorems/544b4c5a-6e3d-5802-9768-86ba6643c333
-- title:
--   Local Field: maximal Unramified le fixed Field
-- statement:
--   The Local Field construction uses the maximal Unramified le fixed Field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Unramified.lean#L175-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Unramified.lean#L175-L179

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_IntermediateField
import Definitions.Def_GroundTheory_LocalFields_UnramifiedDefs
import Definitions.Def_GroundTheory_LocalFields_UnramifiedHensel
import Definitions.Def_GroundTheory_LocalFields_Unramified
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
open ValuativeRel IsLocalRing Polynomial
open scoped _root_.IntermediateField
open GroundTheory GroundTheory.LocalField
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.maximalUnramified_le_fixedField :
    maximalUnramified K L ≤ IntermediateField.fixedField (inertiaSubgroup K L) := by sorry
