-- Prove2me | Theorems.Thm_GroundTheory_Global_measurePreserving_mapComplexCoord
-- name    : GroundTheory.Global.measurePreserving_mapComplexCoord
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:22.69178+00:00
-- url     : https://prove2.me/theorems/9139620d-c4b0-4435-abcb-24548b7b22b1
-- title:
--   Global: measure Preserving map Complex Coord
-- statement:
--   The Global construction uses the measure Preserving map Complex Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L35-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L35-L51

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

theorem GroundTheory.Global.measurePreserving_mapComplexCoord (a : ℂ ≃L[ℝ] ℂ)
    (ha : |LinearMap.det (a : ℂ →ₗ[ℝ] ℂ)| = 2) :
    MeasurePreserving (mapComplexCoord K a) (selfDualMeasure K) volume := by sorry
