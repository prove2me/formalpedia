-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_form_apply_apply_complex
-- name    : GlobalTheory.isoTransvection.form_apply_apply_complex
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:01:28.937574+00:00
-- url     : https://prove2.me/theorems/74ec3340-1002-457f-9dda-70d2ddc5ce99
-- title:
--   iso Transvection: form apply apply complex
-- statement:
--   The iso Transvection construction uses the form apply apply complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L257-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L257-L260

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

theorem GlobalTheory.isoTransvection.form_apply_apply_complex (hh : ∀ u v, h v u = star (h u v)) (b : ℂ) (u v : W) :
    h (isoTransvection h x hx b u) (isoTransvection h x hx b v)
      = h u v + (2 * b.re : ℝ) * h u x * h x v := by sorry
