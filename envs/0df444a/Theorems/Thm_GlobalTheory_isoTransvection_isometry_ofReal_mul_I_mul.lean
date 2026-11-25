-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_isometry_ofReal_mul_I_mul
-- name    : GlobalTheory.isoTransvection.isometry_ofReal_mul_I_mul
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:47:59.839939+00:00
-- url     : https://prove2.me/theorems/42b8c2ca-ff21-598f-bbd7-aa694f6b34b2
-- title:
--   iso Transvection: isometry of Real mul I mul
-- statement:
--   The iso Transvection construction uses the isometry of Real mul I mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L287-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L287-L290

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_DifferentiableToContinuousLinearMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Module
open GlobalTheory.isoTransvection
variable {W : Type*} [AddCommGroup W] [Module ℂ W] {h : W →ₗ[ℂ] W →ₗ⋆[ℂ] ℂ} (x : W)
  (hx : h x x = 0)

theorem GlobalTheory.isoTransvection.isometry_ofReal_mul_I_mul (hh : ∀ u v, h v u = star (h u v)) (b s : ℝ) (u v : W) :
    h (isoTransvection h x hx (b * (Complex.I * s)) u)
      (isoTransvection h x hx (b * (Complex.I * s)) v) = h u v := by sorry
