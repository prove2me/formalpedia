-- Prove2me | Theorems.Thm_GroundTheory_Global_mixedFourier_eq
-- name    : GroundTheory.Global.mixedFourier_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:24:07.364096+00:00
-- url     : https://prove2.me/theorems/90345fe4-f930-4614-a9c4-eca559c6430e
-- title:
--   Global: mixed Fourier eq
-- statement:
--   The Global construction uses the mixed Fourier eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L129-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L129-L134

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

theorem GroundTheory.Global.mixedFourier_eq (f : mixedSpace K → E) (y : mixedSpace K) :
    mixedFourier K f y = 𝓕 (f ∘ (mixedToEuclidean K).symm) (mixedToEuclideanConj K y) := by sorry
