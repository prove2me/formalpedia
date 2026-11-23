-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_pointMatrix_mul_leftMulMatrix
-- name    : GlobalTheory.KeyKa.pointMatrix_mul_leftMulMatrix
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:04:42.880272+00:00
-- url     : https://prove2.me/theorems/ce148d54-48b8-4158-997d-f9ee28e37058
-- title:
--   Key Ka: point Matrix mul left Mul Matrix
-- statement:
--   The Key Ka construction uses the point Matrix mul left Mul Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/PointMatrixMulLeftMulMatrix.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/PointMatrixMulLeftMulMatrix.lean#L7-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_KeyFormula_DegProd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaLawProofs_PointMatrixMulLeftMulMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.KeyKa
open GlobalTheory GlobalTheory.KeyKa

theorem GlobalTheory.KeyKa.pointMatrix_mul_leftMulMatrix {O B Ix : Type} [CommRing O] [CommRing B] [Algebra O B]
    [Fintype Ix] [DecidableEq Ix] (β : Module.Basis Ix O B) (e : Ix → (B →ₐ[O] O)) (y : B) :
    (Matrix.of fun a a' => e a (β a')) * Algebra.leftMulMatrix β y
      = Matrix.diagonal (fun a => e a y) * (Matrix.of fun a a' => e a (β a')) := by sorry
