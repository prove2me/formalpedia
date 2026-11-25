-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GJMatrix_mixedFourierPiSchwartz_apply
-- name    : GroundTheory.Automorphic.GJMatrix.mixedFourierPiSchwartz_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:55:58.557296+00:00
-- url     : https://prove2.me/theorems/1dc1cbc9-728e-483d-810f-4f941aabefe4
-- title:
--   GJMatrix: mixed Fourier Pi Schwartz apply
-- statement:
--   The GJMatrix construction uses the mixed Fourier Pi Schwartz apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L142-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L142-L146

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

theorem GroundTheory.Automorphic.GJMatrix.mixedFourierPiSchwartz_apply (f : 𝓢(ι → mixedSpace K, ℂ)) :
    ⇑(mixedFourierPiSchwartz K f) = mixedFourierPi K f := by sorry
