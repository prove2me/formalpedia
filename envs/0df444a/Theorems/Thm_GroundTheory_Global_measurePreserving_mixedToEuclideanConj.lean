-- Prove2me | Theorems.Thm_GroundTheory_Global_measurePreserving_mixedToEuclideanConj
-- name    : GroundTheory.Global.measurePreserving_mixedToEuclideanConj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:38.737804+00:00
-- url     : https://prove2.me/theorems/892d4cf1-d6d1-4a12-aaf0-a7795f7380e8
-- title:
--   Global: measure Preserving mixed To Euclidean Conj
-- statement:
--   The Global construction uses the measure Preserving mixed To Euclidean Conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L85-L88

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

theorem GroundTheory.Global.measurePreserving_mixedToEuclideanConj :
    MeasurePreserving (mixedToEuclideanConj K) (selfDualMeasure K) volume := by sorry
