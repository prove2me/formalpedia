-- Prove2me | Theorems.Thm_GroundTheory_LocalField_map_upperRamificationGroup
-- name    : GroundTheory.LocalField.map_upperRamificationGroup
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:53:10.877961+00:00
-- url     : https://prove2.me/theorems/7598aba3-eeae-4f56-8a7a-a1a503a36927
-- title:
--   Local Field: map upper Ramification Group
-- statement:
--   The Local Field construction uses the map upper Ramification Group property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UpperNumbering.lean#L216-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UpperNumbering.lean#L216-L221

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
import Definitions.Def_GroundTheory_LocalFields_LowerIndexQuotient
import Definitions.Def_GroundTheory_LocalFields_UpperNumbering
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
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable [IsGalois K L] (M : IntermediateField K L) [IsGalois K M]

theorem GroundTheory.LocalField.map_upperRamificationGroup (v : ℝ) :
    (upperRamificationGroup K L v).map (AlgEquiv.restrictNormalHom M) =
      upperRamificationGroup K M v := by sorry
