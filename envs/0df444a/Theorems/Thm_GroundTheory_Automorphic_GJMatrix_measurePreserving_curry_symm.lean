-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GJMatrix_measurePreserving_curry_symm
-- name    : GroundTheory.Automorphic.GJMatrix.measurePreserving_curry_symm
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:42:45.13913+00:00
-- url     : https://prove2.me/theorems/7e56c232-c575-47e3-8375-da0e7c3e4c5c
-- title:
--   GJMatrix: measure Preserving curry symm
-- statement:
--   The GJMatrix construction uses the measure Preserving curry symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L13-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixInfinite.lean#L13-L27

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

theorem GroundTheory.Automorphic.GJMatrix.measurePreserving_curry_symm {α κ X : Type*} [Fintype α] [Fintype κ] [MeasurableSpace X]
    (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (MeasurableEquiv.curry α κ X).symm
      (Measure.pi fun _ : α ↦ Measure.pi fun _ : κ ↦ μ) (Measure.pi fun _ : α × κ ↦ μ) := by sorry
