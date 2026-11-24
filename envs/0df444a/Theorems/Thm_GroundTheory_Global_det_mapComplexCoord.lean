-- Prove2me | Theorems.Thm_GroundTheory_Global_det_mapComplexCoord
-- name    : GroundTheory.Global.det_mapComplexCoord
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:40:40.820648+00:00
-- url     : https://prove2.me/theorems/8c736c25-b1c9-40f0-bf9d-51abeb0789c6
-- title:
--   Global: det map Complex Coord
-- statement:
--   The Global construction uses the det map Complex Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L25-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L25-L33

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

theorem GroundTheory.Global.det_mapComplexCoord (a : ℂ ≃L[ℝ] ℂ) :
    LinearMap.det (mapComplexCoord K a : mixedSpace K →ₗ[ℝ] mixedSpace K) =
      LinearMap.det (a : ℂ →ₗ[ℝ] ℂ) ^ nrComplexPlaces K := by sorry
