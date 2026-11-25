-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Adele2_mixedPairing2_eq_inner
-- name    : GroundTheory.Automorphic.Adele2.mixedPairing2_eq_inner
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:43:32.218231+00:00
-- url     : https://prove2.me/theorems/1cfd947c-e70e-4748-a19a-63910b16d355
-- title:
--   Adele2: mixed Pairing2 eq inner
-- statement:
--   The Adele2 construction uses the mixed Pairing2 eq inner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L50-L53

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

theorem GroundTheory.Automorphic.Adele2.mixedPairing2_eq_inner (x y : Fin 2 → mixedSpace K) :
    mixedPairing2 K x y = ⟪toEuclid2 K x, toEuclid2Conj K y⟫ := by sorry
