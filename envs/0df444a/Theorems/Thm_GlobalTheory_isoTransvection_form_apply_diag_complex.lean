-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_form_apply_diag_complex
-- name    : GlobalTheory.isoTransvection.form_apply_diag_complex
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:01:37.179511+00:00
-- url     : https://prove2.me/theorems/cb584984-0db3-420c-98a0-40e9ba18014b
-- title:
--   iso Transvection: form apply diag complex
-- statement:
--   The iso Transvection construction uses the form apply diag complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L262-L267
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L262-L267

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

theorem GlobalTheory.isoTransvection.form_apply_diag_complex (hh : ∀ u v, h v u = star (h u v)) (b : ℂ) (v : W) :
    h (isoTransvection h x hx b v) (isoTransvection h x hx b v)
      = h v v + ((2 * b.re * ‖h v x‖ ^ 2 : ℝ) : ℂ) := by sorry
