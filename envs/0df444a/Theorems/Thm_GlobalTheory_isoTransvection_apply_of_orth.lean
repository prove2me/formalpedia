-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_apply_of_orth
-- name    : GlobalTheory.isoTransvection.apply_of_orth
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:40.615272+00:00
-- url     : https://prove2.me/theorems/55d12d9b-5830-4a84-b00b-b61c194c51ba
-- title:
--   iso Transvection: apply of orth
-- statement:
--   The iso Transvection construction uses the apply of orth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L32-L33

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

theorem GlobalTheory.isoTransvection.apply_of_orth (b : R) {v : M} (hv : h v x = 0) : isoTransvection h x hx b v = v := by sorry
