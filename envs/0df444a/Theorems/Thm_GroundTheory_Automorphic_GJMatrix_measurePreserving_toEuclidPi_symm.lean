-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GJMatrix_measurePreserving_toEuclidPi_symm
-- name    : GroundTheory.Automorphic.GJMatrix.measurePreserving_toEuclidPi_symm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:57:22.987801+00:00
-- url     : https://prove2.me/theorems/acbb43be-e7a6-47f4-90b6-014b3b279e30
-- title:
--   GJMatrix: measure Preserving to Euclid Pi symm
-- statement:
--   The GJMatrix construction uses the measure Preserving to Euclid Pi symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L110-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L110-L114

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_TraceLatticePoisson
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open GroundTheory.Global NumberField NumberField.mixedEmbedding MeasureTheory Module Filter
open scoped FourierTransform SchwartzMap RealInnerProductSpace nonZeroDivisors Classical
set_option synthInstance.maxSize 1000
noncomputable section
variable (K : Type*) [Field K] [NumberField K]
variable {ι : Type*} [Fintype ι]

theorem GroundTheory.Automorphic.GJMatrix.measurePreserving_toEuclidPi_symm :
    MeasurePreserving (toEuclidPi K (ι := ι)).symm volume (mixedMeasurePi K) := by sorry
