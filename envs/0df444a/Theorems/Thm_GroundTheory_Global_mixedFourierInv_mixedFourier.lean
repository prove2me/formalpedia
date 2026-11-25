-- Prove2me | Theorems.Thm_GroundTheory_Global_mixedFourierInv_mixedFourier
-- name    : GroundTheory.Global.mixedFourierInv_mixedFourier
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:55:58.928135+00:00
-- url     : https://prove2.me/theorems/333e4684-e438-54d6-bc86-108928f1b73d
-- title:
--   Global: mixed Fourier Inv mixed Fourier
-- statement:
--   The Global construction uses the mixed Fourier Inv mixed Fourier property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L156-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L156-L168

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
variable [CompleteSpace E]

theorem GroundTheory.Global.mixedFourierInv_mixedFourier (f : 𝓢(mixedSpace K, E)) (x : mixedSpace K) :
    mixedFourierInv K (mixedFourier K f) x = f x := by sorry
