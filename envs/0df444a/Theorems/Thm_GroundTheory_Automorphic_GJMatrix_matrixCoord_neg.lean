-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GJMatrix_matrixCoord_neg
-- name    : GroundTheory.Automorphic.GJMatrix.matrixCoord_neg
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:49.027406+00:00
-- url     : https://prove2.me/theorems/050ad27c-408d-446d-847b-5a8aa618cd8e
-- title:
--   GJMatrix: matrix Coord neg
-- statement:
--   The GJMatrix construction uses the matrix Coord neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixCoord.lean#L31-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixCoord.lean#L31-L31

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
omit [Fintype n]

theorem GroundTheory.Automorphic.GJMatrix.matrixCoord_neg [Neg X] (x : Matrix n n X) : matrixCoord (-x) = -matrixCoord x := by sorry
