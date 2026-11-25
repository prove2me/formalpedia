-- Prove2me | Theorems.Thm_GroundTheory_LocalField_herbrandPsi_strictMono
-- name    : GroundTheory.LocalField.herbrandPsi_strictMono
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T08:42:09.824622+00:00
-- url     : https://prove2.me/theorems/fc81967e-07f0-4e74-99f4-88937923d000
-- title:
--   Local Field: herbrand Psi strict Mono
-- statement:
--   The Local Field construction uses the herbrand Psi strict Mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandFunction.lean#L318-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HerbrandFunction.lean#L318-L319

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

theorem GroundTheory.LocalField.herbrandPsi_strictMono : StrictMono (herbrandPsi K L) := by sorry
