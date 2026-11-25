-- Prove2me | Theorems.Thm_GlobalTheory_PadicComplexHost_inv_p_lt_one
-- name    : GlobalTheory.PadicComplexHost.inv_p_lt_one
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:41:50.36591+00:00
-- url     : https://prove2.me/theorems/2df906a1-ddd5-557d-b71d-f488938ea711
-- title:
--   Padic Complex Host: inv p lt one
-- statement:
--   The Padic Complex Host construction uses the inv p lt one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ValuationCoeEqNorm.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ValuationCoeEqNorm.lean#L18-L19

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

theorem GlobalTheory.PadicComplexHost.inv_p_lt_one : (p : ℝ)⁻¹ < 1 := by sorry
