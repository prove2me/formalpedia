-- Prove2me | Theorems.Thm_GroundTheory_LocalField_upperRamificationGroup_antitone
-- name    : GroundTheory.LocalField.upperRamificationGroup_antitone
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:01:50.284027+00:00
-- url     : https://prove2.me/theorems/7c19e885-2b58-45e5-a1ee-083d0c95441d
-- title:
--   Local Field: upper Ramification Group antitone
-- statement:
--   The Local Field construction uses the upper Ramification Group antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandFunction.lean#L429-L430
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandFunction.lean#L429-L430

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_LowerIndex
import Definitions.Def_GroundTheory_LocalFields_HerbrandFunction
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
open ValuativeRel Filter Topology MeasureTheory
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable {K L}
variable (K L)

theorem GroundTheory.LocalField.upperRamificationGroup_antitone : Antitone (upperRamificationGroup K L) := by sorry
