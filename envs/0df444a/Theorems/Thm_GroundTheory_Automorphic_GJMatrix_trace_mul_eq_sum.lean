-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_GJMatrix_trace_mul_eq_sum
-- name    : GroundTheory.Automorphic.GJMatrix.trace_mul_eq_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:58:36.77742+00:00
-- url     : https://prove2.me/theorems/41517010-c730-4aff-a51d-e8fd59ae92c5
-- title:
--   GJMatrix: trace mul eq sum
-- statement:
--   The GJMatrix construction uses the trace mul eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixCoord.lean#L73-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/GL2/GJMatrixCoord.lean#L73-L76

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

theorem GroundTheory.Automorphic.GJMatrix.trace_mul_eq_sum {R : Type*} [CommRing R] (x y : Matrix n n R) :
    trace (x * y) = ∑ p, matrixCoord x p * matrixCoordT y p := by sorry
