-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Adele2_toEuclid2Conj_apply
-- name    : GroundTheory.Automorphic.Adele2.toEuclid2Conj_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:54:57.844402+00:00
-- url     : https://prove2.me/theorems/0d37c566-c5b8-4205-9404-02ace7436a77
-- title:
--   Adele2: to Euclid2 Conj apply
-- statement:
--   The Adele2 construction uses the to Euclid2 Conj apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/SummableNormIffAndTsumEqCoset2.lean#L46-L48

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

theorem GroundTheory.Automorphic.Adele2.toEuclid2Conj_apply (x : Fin 2 → mixedSpace K) :
    toEuclid2Conj K x =
      WithLp.toLp 2 (mixedToEuclideanConj K (x 0), mixedToEuclideanConj K (x 1)) := by sorry
