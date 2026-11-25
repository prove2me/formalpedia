-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsUnramifiedSubextension_ramificationIndex_eq_one
-- name    : GroundTheory.LocalField.IsUnramifiedSubextension.ramificationIndex_eq_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:49:14.553022+00:00
-- url     : https://prove2.me/theorems/f84e9593-f2e7-49ba-aa09-f900ba4defbe
-- title:
--   Is Unramified Subextension: ramification Index eq one
-- statement:
--   The Is Unramified Subextension construction uses the ramification Index eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedExistence.lean#L67-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UnramifiedExistence.lean#L67-L70

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
import Definitions.Def_GroundTheory_LocalFields_Integers
import Definitions.Def_GroundTheory_LocalFields_UnitsPowers
import Definitions.Def_GroundTheory_LocalFields_UnramifiedRootsOfUnity
import Definitions.Def_GroundTheory_LocalFields_UnramifiedGalois
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
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
open ValuativeRel IntermediateField
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ksep : Type*} [Field Ksep] [Algebra K Ksep]
omit [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem GroundTheory.LocalField.IsUnramifiedSubextension.ramificationIndex_eq_one {E : IntermediateField K Ksep}
    (hE : IsUnramifiedSubextension E) [ValuativeRel E] [TopologicalSpace E]
    [IsNonarchimedeanLocalField E] [ValuativeExtension K E] : ramificationIndex K E = 1 := by sorry
