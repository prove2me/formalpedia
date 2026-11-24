-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_isometry_iff
-- name    : GlobalTheory.isoTransvection.isometry_iff
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:01:37.644928+00:00
-- url     : https://prove2.me/theorems/e9f1f3f4-4c13-4651-be4d-c095f6744a0e
-- title:
--   iso Transvection: isometry iff
-- statement:
--   The iso Transvection construction uses the isometry iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L135-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L135-L143

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
variable {R M : Type*} [CommRing R] [StarRing R] [AddCommGroup M] [Module R M]
open GlobalTheory.isoTransvection
variable (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0)
variable {h}

theorem GlobalTheory.isoTransvection.isometry_iff [NoZeroDivisors R] (hh : ∀ u v, h v u = star (h u v))
    (hx0 : ∃ v, h v x ≠ 0) (b : R) :
    (∀ u v, h (isoTransvection h x hx b u) (isoTransvection h x hx b v) = h u v)
      ↔ b + star b = 0 := by sorry
