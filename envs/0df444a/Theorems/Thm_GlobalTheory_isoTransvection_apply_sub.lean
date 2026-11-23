-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_apply_sub
-- name    : GlobalTheory.isoTransvection.apply_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:31.664163+00:00
-- url     : https://prove2.me/theorems/1fdf7c07-f99c-44dd-89e0-8031afc12153
-- title:
--   iso Transvection: apply sub
-- statement:
--   The iso Transvection construction uses the apply sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L23-L24

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

theorem GlobalTheory.isoTransvection.apply_sub (b : R) (v : M) : isoTransvection h x hx b v - v = (b * h v x) • x := by sorry
