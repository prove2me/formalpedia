-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_isAdjointPair
-- name    : GlobalTheory.isoTransvection.isAdjointPair
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:47:54.987339+00:00
-- url     : https://prove2.me/theorems/243f8ecd-05bc-5582-8556-4ec4969bb116
-- title:
--   iso Transvection: is Adjoint Pair
-- statement:
--   The iso Transvection construction uses the is Adjoint Pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L123-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L123-L125

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

theorem GlobalTheory.isoTransvection.isAdjointPair (hh : ∀ u v, h v u = star (h u v)) (b : R) :
    LinearMap.IsAdjointPair h h (isoTransvection h x hx b) (isoTransvection h x hx (star b)) := by sorry
