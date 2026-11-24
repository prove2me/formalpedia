-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_injective
-- name    : GlobalTheory.isoTransvection.injective
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:01:27.243778+00:00
-- url     : https://prove2.me/theorems/1792981d-d87a-4e95-b4c0-b33e43c133c2
-- title:
--   iso Transvection: injective
-- statement:
--   The iso Transvection construction uses the injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L147-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L147-L154

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

theorem GlobalTheory.isoTransvection.injective [IsDomain R] [IsTorsionFree R M] (hx0 : ∃ v, h v x ≠ 0) :
    Function.Injective (isoTransvection h x hx) := by sorry
