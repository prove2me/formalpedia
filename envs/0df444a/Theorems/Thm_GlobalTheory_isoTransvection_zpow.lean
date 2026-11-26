-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_zpow
-- name    : GlobalTheory.isoTransvection.zpow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:48:36.523843+00:00
-- url     : https://prove2.me/theorems/d5c0bf42-d4c5-4cbb-ab9d-2801f9d6c05a
-- title:
--   iso Transvection: zpow
-- statement:
--   The iso Transvection construction uses the zpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L85-L88

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

theorem GlobalTheory.isoTransvection.zpow (b : R) (n : ℤ) :
    isoTransvection h x hx b ^ n = isoTransvection h x hx (n * b) := by sorry
