-- Prove2me | Theorems.Thm_GlobalTheory_PadicComplexHost_valuation_coe_eq_norm
-- name    : GlobalTheory.PadicComplexHost.valuation_coe_eq_norm
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:43:34.468806+00:00
-- url     : https://prove2.me/theorems/faaeb3c8-f6bd-4bf2-8484-3b551430f391
-- title:
--   Padic Complex Host: valuation coe eq norm
-- statement:
--   The Padic Complex Host construction uses the valuation coe eq norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ValuationCoeEqNorm.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ValuationCoeEqNorm.lean#L11-L13

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

theorem GlobalTheory.PadicComplexHost.valuation_coe_eq_norm (x : ℂ_[p]) : ((Valued.v x : NNReal) : ℝ) = ‖x‖ := by sorry
