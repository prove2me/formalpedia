-- Prove2me | Theorems.Thm_GroundTheory_LocalField_herbrandPhi_of_mem_Icc
-- name    : GroundTheory.LocalField.herbrandPhi_of_mem_Icc
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:39:28.75461+00:00
-- url     : https://prove2.me/theorems/b62e911b-53cb-4680-8478-f755b086ecf5
-- title:
--   Local Field: herbrand Phi of mem Icc
-- statement:
--   The Local Field construction uses the herbrand Phi of mem Icc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandFunction.lean#L344-L386
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandFunction.lean#L344-L386

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

theorem GroundTheory.LocalField.herbrandPhi_of_mem_Icc (n : ℕ) {u : ℝ} (hu : u ∈ Set.Icc (n : ℝ) (n + 1)) :
    herbrandPhi K L u = herbrandPhi K L n +
      (u - n) / ((lowerRamificationGroup K L ((n : ℤ) + 1)).relIndex
        (lowerRamificationGroup K L 0) : ℝ) := by sorry
