-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_commute
-- name    : GlobalTheory.isoTransvection.commute
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:06.152264+00:00
-- url     : https://prove2.me/theorems/bd148788-c71f-4595-bf30-5e47409a4889
-- title:
--   iso Transvection: commute
-- statement:
--   The iso Transvection construction uses the commute property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L51-L53

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

theorem GlobalTheory.isoTransvection.commute (b b' : R) :
    Commute (isoTransvection h x hx b) (isoTransvection h x hx b') := by sorry
