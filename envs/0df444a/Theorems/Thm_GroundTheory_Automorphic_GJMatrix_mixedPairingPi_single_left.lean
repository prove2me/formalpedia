-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mixedPairingPi_single_left
-- name    : GroundTheory.Automorphic.GJMatrix.mixedPairingPi_single_left
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:55:47.245915+00:00
-- url     : https://prove2.me/theorems/4a3a6bd7-ba5f-43a3-b996-14dabaf1c262
-- title:
--   GJMatrix: mixed Pairing Pi single left
-- statement:
--   The GJMatrix construction uses the mixed Pairing Pi single left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L272-L275
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L272-L275

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
variable {K}

theorem GroundTheory.Automorphic.GJMatrix.mixedPairingPi_single_left (i : ι) (x : mixedSpace K) (y : ι → mixedSpace K) :
    mixedPairingPi K (Pi.single i x) y = mixedTraceForm K x (y i) := by sorry
