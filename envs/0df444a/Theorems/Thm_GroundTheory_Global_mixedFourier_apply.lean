-- Prove2me | Theorems.Thm_GroundTheory_Global_mixedFourier_apply
-- name    : GroundTheory.Global.mixedFourier_apply
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:42:39.30131+00:00
-- url     : https://prove2.me/theorems/04b742a9-d1ff-4805-bcfb-3ad998605c82
-- title:
--   Global: mixed Fourier apply
-- statement:
--   The Global construction uses the mixed Fourier apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L121-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L121-L122

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem GroundTheory.Global.mixedFourier_apply (f : mixedSpace K → E) (y : mixedSpace K) :
    mixedFourier K f y = ∫ x, 𝐞 (-mixedTraceForm K x y) • f x ∂selfDualMeasure K := by sorry
