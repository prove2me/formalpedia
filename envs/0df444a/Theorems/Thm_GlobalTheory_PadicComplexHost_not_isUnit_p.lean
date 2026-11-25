-- Prove2me | Theorems.Thm_GlobalTheory_PadicComplexHost_not_isUnit_p
-- name    : GlobalTheory.PadicComplexHost.not_isUnit_p
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T16:41:25.576046+00:00
-- url     : https://prove2.me/theorems/4dc59969-6f6a-5b9b-9125-adefefdb5ced
-- title:
--   Padic Complex Host: not is Unit p
-- statement:
--   The Padic Complex Host construction uses the not is Unit p property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ValuationCoeEqNorm.lean#L26-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ValuationCoeEqNorm.lean#L26-L34

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

theorem GlobalTheory.PadicComplexHost.not_isUnit_p : ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p]) := by sorry
