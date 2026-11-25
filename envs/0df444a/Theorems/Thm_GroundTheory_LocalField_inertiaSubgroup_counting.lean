-- Prove2me | Theorems.Thm_GroundTheory_LocalField_inertiaSubgroup_counting
-- name    : GroundTheory.LocalField.inertiaSubgroup_counting
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:49:59.645362+00:00
-- url     : https://prove2.me/theorems/57061119-2352-5f21-8d9d-67932c17b920
-- title:
--   Local Field: inertia Subgroup counting
-- statement:
--   The Local Field construction uses the inertia Subgroup counting property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Unramified.lean#L183-L227
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Unramified.lean#L183-L227

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
variable [IsGalois K L]

theorem GroundTheory.LocalField.inertiaSubgroup_counting :
    Nat.card (inertiaSubgroup K L) = ramificationIndex K L ∧
      Nat.card (residueAlgEquiv K L).range = residueDegree K L ∧
      Module.finrank K (IntermediateField.fixedField (inertiaSubgroup K L)) = residueDegree K L := by sorry
