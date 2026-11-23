-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_form_apply_apply
-- name    : GlobalTheory.isoTransvection.form_apply_apply
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:26.209933+00:00
-- url     : https://prove2.me/theorems/3e69df59-bb0b-4160-81d0-d4d7ba3d8152
-- title:
--   iso Transvection: form apply apply
-- statement:
--   The iso Transvection construction uses the form apply apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L102-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L102-L106

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

theorem GlobalTheory.isoTransvection.form_apply_apply (hh : ∀ u v, h v u = star (h u v)) (b : R) (u v : M) :
    h (isoTransvection h x hx b u) (isoTransvection h x hx b v)
      = h u v + (b + star b) * h u x * h x v := by sorry
