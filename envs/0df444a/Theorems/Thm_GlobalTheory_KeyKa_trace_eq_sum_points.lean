-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_trace_eq_sum_points
-- name    : GlobalTheory.KeyKa.trace_eq_sum_points
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:48:53.781049+00:00
-- url     : https://prove2.me/theorems/0503f802-0cb7-492b-b0a9-a2af45df977d
-- title:
--   Key Ka: trace eq sum points
-- statement:
--   The Key Ka construction uses the trace eq sum points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/PointMatrixMulLeftMulMatrix.lean#L20-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/PointMatrixMulLeftMulMatrix.lean#L20-L34

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

theorem GlobalTheory.KeyKa.trace_eq_sum_points {O B Ix : Type} [CommRing O] [IsDomain O] [CommRing B] [Algebra O B]
    [Fintype Ix] [DecidableEq Ix] (β : Module.Basis Ix O B) (e : Ix → (B →ₐ[O] O))
    (h : (Matrix.of fun a a' => e a (β a')).det ≠ 0) (y : B) :
    Algebra.trace O B y = ∑ a, e a y := by sorry
