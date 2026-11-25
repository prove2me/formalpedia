-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Adele2_measurePreserving_toEuclid2_symm
-- name    : GroundTheory.Automorphic.Adele2.measurePreserving_toEuclid2_symm
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:47:54.173894+00:00
-- url     : https://prove2.me/theorems/65eaa2f5-2d78-4240-ab00-c686735ac5f2
-- title:
--   Adele2: measure Preserving to Euclid2 symm
-- statement:
--   The Adele2 construction uses the measure Preserving to Euclid2 symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L77-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L77-L81

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

theorem GroundTheory.Automorphic.Adele2.measurePreserving_toEuclid2_symm :
    MeasurePreserving (toEuclid2 K).symm volume (mixedMeasure2 K) := by sorry
