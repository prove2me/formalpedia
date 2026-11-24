-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_autMat_mulVec
-- name    : GlobalTheory.LevDesc.autMat_mulVec
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:16.533363+00:00
-- url     : https://prove2.me/theorems/1856a0bf-569b-44bf-97d6-70796b39bd34
-- title:
--   Lev Desc: aut Mat mul Vec
-- statement:
--   The Lev Desc construction uses the aut Mat mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L359-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L359-L360

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsRightActFunPull
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.LevDesc
variable {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] {r p : ℕ} (e : M ≃+ (Fin r → ZMod p))

theorem GlobalTheory.LevDesc.autMat_mulVec (γ : M ≃ₗ[O] M) (x : M) :
    (autMat e γ : Matrix (Fin r) (Fin r) (ZMod p)).mulVec (e x) = e (γ x) := by sorry
