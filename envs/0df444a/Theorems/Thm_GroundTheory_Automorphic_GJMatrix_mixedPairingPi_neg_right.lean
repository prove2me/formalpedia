-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mixedPairingPi_neg_right
-- name    : GroundTheory.Automorphic.GJMatrix.mixedPairingPi_neg_right
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:55:41.937019+00:00
-- url     : https://prove2.me/theorems/0565f0d8-0e2d-4d1f-bbcf-a935992b6dcc
-- title:
--   GJMatrix: mixed Pairing Pi neg right
-- statement:
--   The GJMatrix construction uses the mixed Pairing Pi neg right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L38-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L38-L40

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

theorem GroundTheory.Automorphic.GJMatrix.mixedPairingPi_neg_right (x y : ι → mixedSpace K) :
    mixedPairingPi K x (-y) = -mixedPairingPi K x y := by sorry
