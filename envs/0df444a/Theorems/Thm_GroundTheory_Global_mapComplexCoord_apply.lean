-- Prove2me | Theorems.Thm_GroundTheory_Global_mapComplexCoord_apply
-- name    : GroundTheory.Global.mapComplexCoord_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:46.899966+00:00
-- url     : https://prove2.me/theorems/77218b55-c104-4452-a6b4-97e352d33a96
-- title:
--   Global: map Complex Coord apply
-- statement:
--   The Global construction uses the map Complex Coord apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L22-L23

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TracePairing
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceFourier
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField NumberField.InfinitePlace NumberField.mixedEmbedding Module MeasureTheory
open scoped Classical ComplexConjugate RealInnerProductSpace FourierTransform Real ENNReal SchwartzMap
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
omit [NumberField K]

theorem GroundTheory.Global.mapComplexCoord_apply (a : ℂ ≃L[ℝ] ℂ) (x : mixedSpace K) :
    mapComplexCoord K a x = (x.1, fun w => a (x.2 w)) := by sorry
