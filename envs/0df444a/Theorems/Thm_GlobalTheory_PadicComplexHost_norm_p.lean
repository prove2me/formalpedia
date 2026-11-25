-- Prove2me | Theorems.Thm_GlobalTheory_PadicComplexHost_norm_p
-- name    : GlobalTheory.PadicComplexHost.norm_p
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:45:06.576274+00:00
-- url     : https://prove2.me/theorems/aefcb077-b55a-4b54-bba0-46f36f360264
-- title:
--   Padic Complex Host: norm p
-- statement:
--   The Padic Complex Host construction uses the norm p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ValuationCoeEqNorm.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ValuationCoeEqNorm.lean#L15-L16

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_DualLattices_ExistsPrimitiveRoot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ValuationCoeEqNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Ideal
open GlobalTheory GlobalTheory.PadicComplexHost
variable (p : ℕ) [hp : Fact p.Prime]

theorem GlobalTheory.PadicComplexHost.norm_p : ‖((p : ℕ) : ℂ_[p])‖ = (p : ℝ)⁻¹ := by sorry
