-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsUnramified_sup
-- name    : GroundTheory.LocalField.IsUnramified.sup
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T13:03:54.856264+00:00
-- url     : https://prove2.me/theorems/6d78e0da-ce7f-4a90-b3c3-915b141a3feb
-- title:
--   Is Unramified: sup
-- statement:
--   The Is Unramified construction uses the sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Unramified.lean#L126-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Unramified.lean#L126-L128

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
variable (K L : Type*) [Field K] [ValuativeRel K] [Field L] [ValuativeRel L]
  [Algebra K L] [ValuativeExtension K L]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] [FiniteDimensional K L]

theorem GroundTheory.LocalField.IsUnramified.sup (E F : IntermediateField K L) [IsUnramified K E] [IsUnramified K F] :
    IsUnramified K (E ⊔ F : IntermediateField K L) := by sorry
