-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_endMat_mulVec
-- name    : GlobalTheory.LevDesc.endMat_mulVec
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:02:48.783946+00:00
-- url     : https://prove2.me/theorems/905c527f-1cec-49a1-a583-93711ea4b6e1
-- title:
--   Lev Desc: end Mat mul Vec
-- statement:
--   The Lev Desc construction uses the end Mat mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L353-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L353-L354

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

theorem GlobalTheory.LevDesc.endMat_mulVec (γ : Module.End O M) (x : M) : (endMat e γ).mulVec (e x) = e (γ x) := by sorry
