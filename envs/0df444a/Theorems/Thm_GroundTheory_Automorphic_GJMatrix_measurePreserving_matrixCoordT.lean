-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GJMatrix_measurePreserving_matrixCoordT
-- name    : GroundTheory.Automorphic.GJMatrix.measurePreserving_matrixCoordT
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:43.416506+00:00
-- url     : https://prove2.me/theorems/bb29b837-91f3-4a64-ab7f-b17199633d66
-- title:
--   GJMatrix: measure Preserving matrix Coord T
-- statement:
--   The GJMatrix construction uses the measure Preserving matrix Coord T property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixCoord.lean#L62-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixCoord.lean#L62-L71

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixCoord
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open MeasureTheory Matrix
noncomputable section
variable {n X : Type*} [Fintype n]

theorem GroundTheory.Automorphic.GJMatrix.measurePreserving_matrixCoordT [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (matrixCoordT : Matrix n n X → n × n → X) (matrixMeasure μ)
      (Measure.pi fun _ : n × n ↦ μ) := by sorry
