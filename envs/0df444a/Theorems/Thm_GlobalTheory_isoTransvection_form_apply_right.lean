-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_form_apply_right
-- name    : GlobalTheory.isoTransvection.form_apply_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:45:39.42125+00:00
-- url     : https://prove2.me/theorems/83d6009e-bd37-4dfc-a9bd-fdef086672d1
-- title:
--   iso Transvection: form apply right
-- statement:
--   The iso Transvection construction uses the form apply right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L96-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L96-L100

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

theorem GlobalTheory.isoTransvection.form_apply_right (hh : ∀ u v, h v u = star (h u v)) (b : R) (u v : M) :
    h u (isoTransvection h x hx b v) = h u v + star b * h u x * h x v := by sorry
