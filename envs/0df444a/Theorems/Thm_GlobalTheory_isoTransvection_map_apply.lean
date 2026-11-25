-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_map_apply
-- name    : GlobalTheory.isoTransvection.map_apply
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:11.618356+00:00
-- url     : https://prove2.me/theorems/6e434858-3166-5e76-8564-9a6e1f397026
-- title:
--   iso Transvection: map apply
-- statement:
--   The iso Transvection construction uses the map apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L171-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L171-L175

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
variable (h)

theorem GlobalTheory.isoTransvection.map_apply {R' M' : Type*} [CommRing R'] [StarRing R'] [AddCommGroup M'] [Module R' M']
    {φ : R →+* R'} (j : M →ₛₗ[φ] M') (h' : M' →ₗ[R'] M' →ₗ⋆[R'] R')
    (hx' : h' (j x) (j x) = 0) (b : R) (v : M) (hj : h' (j v) (j x) = φ (h v x)) :
    j (isoTransvection h x hx b v) = isoTransvection h' (j x) hx' (φ b) (j v) := by sorry
