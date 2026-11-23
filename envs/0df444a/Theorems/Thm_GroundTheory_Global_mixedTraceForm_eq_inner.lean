-- Prove2me | Theorems.Thm_GroundTheory_Global_mixedTraceForm_eq_inner
-- name    : GroundTheory.Global.mixedTraceForm_eq_inner
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:56.652029+00:00
-- url     : https://prove2.me/theorems/4d388636-a57b-4b77-b9a3-eb3c0f1b25d0
-- title:
--   Global: mixed Trace Form eq inner
-- statement:
--   The Global construction uses the mixed Trace Form eq inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L96-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L96-L111

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

theorem GroundTheory.Global.mixedTraceForm_eq_inner (x y : mixedSpace K) :
    mixedTraceForm K x y = ⟪mixedToEuclidean K x, mixedToEuclideanConj K y⟫ := by sorry
