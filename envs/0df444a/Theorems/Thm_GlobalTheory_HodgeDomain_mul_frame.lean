-- Prove2me | Theorems.Thm_GlobalTheory_HodgeDomain_mul_frame
-- name    : GlobalTheory.HodgeDomain.mul_frame
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:07:52.552571+00:00
-- url     : https://prove2.me/theorems/1197eb40-6a2e-42f9-bcd7-313595b73c2a
-- title:
--   Hodge Domain: mul frame
-- statement:
--   The Hodge Domain construction uses the mul frame property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/HPInvEqForm.lean#L227-L237
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/HPInvEqForm.lean#L227-L237

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_HPInvEqForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG
open scoped ComplexOrder
open GlobalTheory GlobalTheory.HodgeDomain
variable {p q : ℕ}

theorem GlobalTheory.HodgeDomain.mul_frame {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) :
    (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * fromBlocks 1 z 0 1 =
      fromBlocks 1 (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) 0 1 *
        fromBlocks (jW g z) 0 (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₂₁ (kapQ g z) := by sorry
