-- Prove2me | Theorems.Thm_GroundTheory_LocalField_finiteDimensional_of_le
-- name    : GroundTheory.LocalField.finiteDimensional_of_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T09:37:37.900395+00:00
-- url     : https://prove2.me/theorems/bb8d618b-65f2-4e49-9683-ac3f0bfb2f50
-- title:
--   Local Field: finite Dimensional of le
-- statement:
--   The Local Field construction uses the finite Dimensional of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/TameExtension.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/TameExtension.lean#L68-L71

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_ExtensionsOfDegree
import Definitions.Def_GroundTheory_LocalFields_RamificationTameStructure
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_SeparableClosure
import Definitions.Def_GroundTheory_LocalFields_UnramifiedExistence
import Definitions.Def_GroundTheory_LocalFields_Unramified
import Definitions.Def_GroundTheory_LocalFields_TameExtension
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

theorem GroundTheory.LocalField.finiteDimensional_of_le {K Ω : Type*} [Field K] [Field Ω] [Algebra K Ω]
    {E F : IntermediateField K Ω} [FiniteDimensional K F] (h : E ≤ F) : FiniteDimensional K E := by sorry
