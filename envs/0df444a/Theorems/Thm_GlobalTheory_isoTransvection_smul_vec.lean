-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_smul_vec
-- name    : GlobalTheory.isoTransvection.smul_vec
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:48:34.0609+00:00
-- url     : https://prove2.me/theorems/0d08e42f-f6a1-4cfb-a48b-390b370c2ed5
-- title:
--   iso Transvection: smul vec
-- statement:
--   The iso Transvection construction uses the smul vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L165-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L165-L169

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

theorem GlobalTheory.isoTransvection.smul_vec (a b : R) (hax : h (a • x) (a • x) = 0 := by simp [*]) :
    isoTransvection h (a • x) hax b = isoTransvection h x hx (b * (a * star a)) := by sorry
