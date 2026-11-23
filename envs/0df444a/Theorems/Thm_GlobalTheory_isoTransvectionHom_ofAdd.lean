-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvectionHom_ofAdd
-- name    : GlobalTheory.isoTransvectionHom_ofAdd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:26.034813+00:00
-- url     : https://prove2.me/theorems/59caef10-37f2-42d0-81bd-776f27fe22cb
-- title:
--   Global Theory: iso Transvection Hom of Add
-- statement:
--   The Global Theory construction uses the iso Transvection Hom of Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L73-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L73-L74

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

theorem GlobalTheory.isoTransvectionHom_ofAdd (h : M →ₗ[R] M →ₗ⋆[R] R) (x : M) (hx : h x x = 0) (b : R) :
    isoTransvectionHom h x hx (Multiplicative.ofAdd b) = isoTransvection h x hx b := by sorry
