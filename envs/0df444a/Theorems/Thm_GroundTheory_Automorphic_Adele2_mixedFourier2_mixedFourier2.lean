-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Adele2_mixedFourier2_mixedFourier2
-- name    : GroundTheory.Automorphic.Adele2.mixedFourier2_mixedFourier2
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:53:13.663229+00:00
-- url     : https://prove2.me/theorems/4c697d4b-e4b3-4548-aac4-6314350266ec
-- title:
--   Adele2: mixed Fourier2 mixed Fourier2
-- statement:
--   The Adele2 construction uses the mixed Fourier2 mixed Fourier2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L139-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L139-L141

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_SummableNormIffAndTsumEqCoset2
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.Adele2
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]

theorem GroundTheory.Automorphic.Adele2.mixedFourier2_mixedFourier2 (f : 𝓢(Fin 2 → mixedSpace K, ℂ))
    (x : Fin 2 → mixedSpace K) : mixedFourier2 K (mixedFourier2 K f) x = f (-x) := by sorry
