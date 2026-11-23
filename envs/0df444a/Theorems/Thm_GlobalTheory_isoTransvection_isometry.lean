-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_isometry
-- name    : GlobalTheory.isoTransvection.isometry
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:51:24.527569+00:00
-- url     : https://prove2.me/theorems/3faa2eb6-cac0-4bc6-9fe9-225568e502de
-- title:
--   iso Transvection: isometry
-- statement:
--   The iso Transvection construction uses the isometry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L131-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L131-L133

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

theorem GlobalTheory.isoTransvection.isometry (hh : ∀ u v, h v u = star (h u v)) {b : R} (hb : b + star b = 0) (u v : M) :
    h (isoTransvection h x hx b u) (isoTransvection h x hx b v) = h u v := by sorry
