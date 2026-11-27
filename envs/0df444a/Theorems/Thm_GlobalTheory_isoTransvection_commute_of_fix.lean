-- Prove2me | Theorems.Thm_GlobalTheory_isoTransvection_commute_of_fix
-- name    : GlobalTheory.isoTransvection.commute_of_fix
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:48:13.057012+00:00
-- url     : https://prove2.me/theorems/0b480171-8765-4787-8d01-1f41453d25a9
-- title:
--   iso Transvection: commute of fix
-- statement:
--   The iso Transvection construction uses the commute of fix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L184-L187
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/DifferentiableToContinuousLinearMap.lean#L184-L187

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

theorem GlobalTheory.isoTransvection.commute_of_fix (g : M ≃ₗ[R] M) (hgx : g x = x) (hg : ∀ u, h (g u) x = h u x) (b : R) :
    Commute g (isoTransvection h x hx b) := by sorry
