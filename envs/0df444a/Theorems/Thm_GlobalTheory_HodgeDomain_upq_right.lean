-- Prove2me | Theorems.Thm_GlobalTheory_HodgeDomain_upq_right
-- name    : GlobalTheory.HodgeDomain.upq_right
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T14:35:53.433688+00:00
-- url     : https://prove2.me/theorems/238ce6c7-7cf5-4590-888b-b1d514402797
-- title:
--   Hodge Domain: upq right
-- statement:
--   The Hodge Domain construction uses the upq right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/HPInvEqForm.lean#L31-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/HPInvEqForm.lean#L31-L43

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

theorem GlobalTheory.HodgeDomain.upq_right {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) :
    (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) * Jpq p q * (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ =
      Jpq p q := by sorry
