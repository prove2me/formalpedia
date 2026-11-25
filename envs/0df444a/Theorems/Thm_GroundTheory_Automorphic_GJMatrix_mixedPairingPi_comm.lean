-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mixedPairingPi_comm
-- name    : GroundTheory.Automorphic.GJMatrix.mixedPairingPi_comm
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T00:42:45.199631+00:00
-- url     : https://prove2.me/theorems/be6bfcee-d3eb-4257-82b1-6a89aa9b2573
-- title:
--   GJMatrix: mixed Pairing Pi comm
-- statement:
--   The GJMatrix construction uses the mixed Pairing Pi comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L34-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L34-L36

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

theorem GroundTheory.Automorphic.GJMatrix.mixedPairingPi_comm (x y : ι → mixedSpace K) :
    mixedPairingPi K x y = mixedPairingPi K y x := by sorry
