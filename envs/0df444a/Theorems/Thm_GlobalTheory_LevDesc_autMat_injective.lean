-- Prove2me | Theorems.Thm_GlobalTheory_LevDesc_autMat_injective
-- name    : GlobalTheory.LevDesc.autMat_injective
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T18:02:16.309651+00:00
-- url     : https://prove2.me/theorems/943b3576-ab68-4d6a-ae16-1410fc7694ec
-- title:
--   Lev Desc: aut Mat injective
-- statement:
--   The Lev Desc construction uses the aut Mat injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L362-L363
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/IsRightActFunPull.lean#L362-L363

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

theorem GlobalTheory.LevDesc.autMat_injective : Function.Injective (autMat (O := O) e) := by sorry
