-- Prove2me | Theorems.Thm_GlobalTheory_HodgeDomain_hP_moeb
-- name    : GlobalTheory.HodgeDomain.hP_moeb
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:59.967187+00:00
-- url     : https://prove2.me/theorems/4b5ade03-337b-4964-9b44-6e7487b20e5c
-- title:
--   Hodge Domain: h P moeb
-- statement:
--   The Hodge Domain construction uses the h P moeb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/HPInvEqForm.lean#L143-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/HPInvEqForm.lean#L143-L176

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

theorem GlobalTheory.HodgeDomain.hP_moeb {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) {z : Matrix (Fin p) (Fin q) ℂ}
    (hz : z ∈ hcDom p q) :
    jW g z * hP z * (jW g z)ᴴ = hP (moeb (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ) z) := by sorry
