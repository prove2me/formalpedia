-- Prove2me | Theorems.Thm_GroundTheory_LocalField_herbrandPsi_comp
-- name    : GroundTheory.LocalField.herbrandPsi_comp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T08:51:06.392241+00:00
-- url     : https://prove2.me/theorems/e56e34e3-a8d4-554b-8d12-e980f6d763ef
-- title:
--   Local Field: herbrand Psi comp
-- statement:
--   The Local Field construction uses the herbrand Psi comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UpperNumbering.lean#L180-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/UpperNumbering.lean#L180-L183

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

theorem GroundTheory.LocalField.herbrandPsi_comp (v : ℝ) :
    herbrandPsi M L (herbrandPsi K M v) = herbrandPsi K L v := by sorry
