-- Prove2me | Theorems.Thm_GlobalTheory_KeyKa_discr_norm_eq_of_points
-- name    : GlobalTheory.KeyKa.discr_norm_eq_of_points
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:49:15.166397+00:00
-- url     : https://prove2.me/theorems/c5538aa1-6490-412c-b587-21953a4d6930
-- title:
--   Key Ka: discr norm eq of points
-- statement:
--   The Key Ka construction uses the discr norm eq of points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/PointMatrixMulLeftMulMatrix.lean#L36-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaLawProofs/PointMatrixMulLeftMulMatrix.lean#L36-L54

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

theorem GlobalTheory.KeyKa.discr_norm_eq_of_points :
    ∀ (O B Ix : Type) [CommRing O] [IsDomain O] [CommRing B] [Algebra O B] [Fintype Ix]
      [DecidableEq Ix] (β : Module.Basis Ix O B) (e : Ix → (B →ₐ[O] O)),
      (Matrix.of fun a a' => e a (β a')).det ≠ 0 →
        Algebra.discr O β = (Matrix.of fun a a' => e a (β a')).det ^ 2 ∧
          ∀ y : B, Algebra.norm O y = ∏ a, e a y := by sorry
