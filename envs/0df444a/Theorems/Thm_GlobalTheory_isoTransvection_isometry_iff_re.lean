-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_isometry_iff_re
-- name    : GlobalTheory.isoTransvection.isometry_iff_re
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:15.457222+00:00
-- url     : https://prove2.me/theorems/432d733a-8170-4a22-a3b2-a6df376452f9
-- title:
--   iso Transvection: isometry iff re
-- statement:
--   The iso Transvection construction uses the isometry iff re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L274-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L274-L278

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

theorem GlobalTheory.isoTransvection.isometry_iff_re (hh : ∀ u v, h v u = star (h u v)) (hx0 : ∃ v, h v x ≠ 0) (b : ℂ) :
    (∀ u v, h (isoTransvection h x hx b u) (isoTransvection h x hx b v) = h u v)
      ↔ b.re = 0 := by sorry
