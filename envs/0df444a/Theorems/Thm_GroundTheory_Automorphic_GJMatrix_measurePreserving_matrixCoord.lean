-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GJMatrix_measurePreserving_matrixCoord
-- name    : GroundTheory.Automorphic.GJMatrix.measurePreserving_matrixCoord
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:56:07.300561+00:00
-- url     : https://prove2.me/theorems/42d894da-aea1-41a3-a00b-60345e51ccc0
-- title:
--   GJMatrix: measure Preserving matrix Coord
-- statement:
--   The GJMatrix construction uses the measure Preserving matrix Coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixCoord.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixCoord.lean#L57-L60

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

theorem GroundTheory.Automorphic.GJMatrix.measurePreserving_matrixCoord [MeasurableSpace X] (μ : Measure X) [SigmaFinite μ] :
    MeasurePreserving (matrixCoord : Matrix n n X → n × n → X) (matrixMeasure μ)
      (Measure.pi fun _ : n × n ↦ μ) := by sorry
