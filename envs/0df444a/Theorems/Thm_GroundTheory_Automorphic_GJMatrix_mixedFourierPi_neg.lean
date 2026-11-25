-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mixedFourierPi_neg
-- name    : GroundTheory.Automorphic.GJMatrix.mixedFourierPi_neg
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:56:25.004179+00:00
-- url     : https://prove2.me/theorems/0c534302-b94a-47f0-915e-766a06dacf72
-- title:
--   GJMatrix: mixed Fourier Pi neg
-- statement:
--   The GJMatrix construction uses the mixed Fourier Pi neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L162-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L162-L167

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

theorem GroundTheory.Automorphic.GJMatrix.mixedFourierPi_neg (f : (ι → mixedSpace K) → ℂ) (x : ι → mixedSpace K) :
    mixedFourierPi K f (-x) = mixedFourierInvPi K f x := by sorry
