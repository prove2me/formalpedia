-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_isometry_of_re
-- name    : GlobalTheory.isoTransvection.isometry_of_re
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:01:22.927413+00:00
-- url     : https://prove2.me/theorems/6f9bf58c-9651-4c0f-abf0-c8a74596df67
-- title:
--   iso Transvection: isometry of re
-- statement:
--   The iso Transvection construction uses the isometry of re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L280-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L280-L282

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

theorem GlobalTheory.isoTransvection.isometry_of_re (hh : ∀ u v, h v u = star (h u v)) {b : ℂ} (hb : b.re = 0) (u v : W) :
    h (isoTransvection h x hx b u) (isoTransvection h x hx b v) = h u v := by sorry
