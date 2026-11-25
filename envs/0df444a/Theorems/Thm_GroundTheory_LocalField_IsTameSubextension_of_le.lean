-- Prove2me | Theorems.Thm_GroundTheory_LocalField_IsTameSubextension_of_le
-- name    : GroundTheory.LocalField.IsTameSubextension.of_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:06:09.162175+00:00
-- url     : https://prove2.me/theorems/c68c88fc-0107-59f0-a5a7-56acae595bc9
-- title:
--   Is Tame Subextension: of le
-- statement:
--   The Is Tame Subextension construction uses the of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/TameExtension.lean#L120-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/TameExtension.lean#L120-L130

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExtensionsOfDegree
import Definitions.Def_GroundTheory_LocalFields_RamificationTameStructure
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_TameExtension
import Theorems.Thm_GroundTheory_LocalField_IsUnramified_of_le

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
open Polynomial IntermediateField ValuativeRel
open GroundTheory GroundTheory.LocalField
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]

theorem GroundTheory.LocalField.IsTameSubextension.of_le {E F : IntermediateField K Ω} (hF : IsTameSubextension F)
    (h : E ≤ F) : IsTameSubextension E := by sorry
