-- Prove2me | Theorems.Thm_GroundTheory_Global_mixedFourierInv_eq
-- name    : GroundTheory.Global.mixedFourierInv_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T23:42:43.445282+00:00
-- url     : https://prove2.me/theorems/e48ad17f-6734-4dfe-89cc-1fb5777c2a45
-- title:
--   Global: mixed Fourier Inv eq
-- statement:
--   The Global construction uses the mixed Fourier Inv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L136-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/TraceFourier.lean#L136-L141

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

theorem GroundTheory.Global.mixedFourierInv_eq (f : mixedSpace K → E) (x : mixedSpace K) :
    mixedFourierInv K f x = 𝓕⁻ (f ∘ (mixedToEuclideanConj K).symm) (mixedToEuclidean K x) := by sorry
