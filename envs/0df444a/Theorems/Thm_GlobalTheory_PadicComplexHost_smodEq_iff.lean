-- Prove2me | Theorems.Thm_GlobalTheory_PadicComplexHost_smodEq_iff
-- name    : GlobalTheory.PadicComplexHost.smodEq_iff
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T16:43:25.440181+00:00
-- url     : https://prove2.me/theorems/aba78b64-683b-4343-8372-96aaaab5e69e
-- title:
--   Padic Complex Host: smod Eq iff
-- statement:
--   The Padic Complex Host construction uses the smod Eq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ValuationCoeEqNorm.lean#L36-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ValuationCoeEqNorm.lean#L36-L42

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

theorem GlobalTheory.PadicComplexHost.smodEq_iff (n : ℕ) (x y : 𝓞_ℂ_[p]) :
    x ≡ y [SMOD ((span {((p : ℕ) : 𝓞_ℂ_[p])}) ^ n • ⊤ : Submodule 𝓞_ℂ_[p] 𝓞_ℂ_[p])] ↔
      ‖(x : ℂ_[p]) - (y : ℂ_[p])‖ ≤ (p : ℝ)⁻¹ ^ n := by sorry
