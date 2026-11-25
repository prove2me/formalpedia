-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Adele2_mixedPairing2_neg_right
-- name    : GroundTheory.Automorphic.Adele2.mixedPairing2_neg_right
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:54:20.330422+00:00
-- url     : https://prove2.me/theorems/fda0fb63-b709-4bbe-b170-30ccf8aa029d
-- title:
--   Adele2: mixed Pairing2 neg right
-- statement:
--   The Adele2 construction uses the mixed Pairing2 neg right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L21-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L21-L23

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

theorem GroundTheory.Automorphic.Adele2.mixedPairing2_neg_right (x y : Fin 2 → mixedSpace K) :
    mixedPairing2 K x (-y) = -mixedPairing2 K x y := by sorry
