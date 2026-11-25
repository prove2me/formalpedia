-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Adele2_mixedFourier2Schwartz_apply
-- name    : GroundTheory.Automorphic.Adele2.mixedFourier2Schwartz_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:48:14.016072+00:00
-- url     : https://prove2.me/theorems/2b799d5c-0b09-4111-96a5-e94e3d0aac01
-- title:
--   Adele2: mixed Fourier2 Schwartz apply
-- statement:
--   The Adele2 construction uses the mixed Fourier2 Schwartz apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L109-L113
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L109-L113

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

theorem GroundTheory.Automorphic.Adele2.mixedFourier2Schwartz_apply (f : 𝓢(Fin 2 → mixedSpace K, ℂ)) :
    ⇑(mixedFourier2Schwartz K f) = mixedFourier2 K f := by sorry
