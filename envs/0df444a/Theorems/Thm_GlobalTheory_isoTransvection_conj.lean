-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_conj
-- name    : GlobalTheory.isoTransvection.conj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:47:53.031798+00:00
-- url     : https://prove2.me/theorems/521ea629-83a5-58fc-bf68-af0ec6651015
-- title:
--   iso Transvection: conj
-- statement:
--   The iso Transvection construction uses the conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L177-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L177-L182

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

theorem GlobalTheory.isoTransvection.conj (g : M ≃ₗ[R] M) (hg : ∀ u v, h (g u) (g v) = h u v) (b : R)
    (hgx : h (g x) (g x) = 0) :
    g * isoTransvection h x hx b * g⁻¹ = isoTransvection h (g x) hgx b := by sorry
