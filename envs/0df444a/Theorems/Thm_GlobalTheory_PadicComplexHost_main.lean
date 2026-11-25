-- Prove2me | Theorems.Thm_GlobalTheory_PadicComplexHost_main
-- name    : GlobalTheory.PadicComplexHost.main
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:49:37.90613+00:00
-- url     : https://prove2.me/theorems/b78815a1-3b7d-42ef-8d0e-d0532796ad30
-- title:
--   Padic Complex Host: main
-- statement:
--   The Padic Complex Host construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ValuationCoeEqNorm.lean#L77-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ValuationCoeEqNorm.lean#L77-L85

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

theorem GlobalTheory.PadicComplexHost.main : ∀ (p : ℕ) [Fact p.Prime], ∃ (_ : Fact ¬IsUnit ((p : ℕ) : 𝓞_ℂ_[p])) (_ : IsAdicComplete (span {((p : ℕ) : 𝓞_ℂ_[p])}) 𝓞_ℂ_[p])
    (ε : PreTilt 𝓞_ℂ_[p] p), (Valued.v : Valuation ℂ_[p] NNReal).Integers 𝓞_ℂ_[p] ∧
      IsPrimitiveRoot (((frobeniusEquiv (PreTilt 𝓞_ℂ_[p] p) p).symm ε).untilt) p := by sorry
