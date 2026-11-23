-- Prove2me | Theorems.Thm_GlobalTheory_HodgeDomain_upq_iff
-- name    : GlobalTheory.HodgeDomain.upq_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:07.677914+00:00
-- url     : https://prove2.me/theorems/5bbb30ef-083e-45f5-ac90-9ad5be87d1ec
-- title:
--   Hodge Domain: upq iff
-- statement:
--   The Hodge Domain construction uses the upq iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/HPInvEqForm.lean#L17-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/HPInvEqForm.lean#L17-L24

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

theorem GlobalTheory.HodgeDomain.upq_iff {g : GL (Fin p ⊕ Fin q) ℂ} : g ∈ Upq p q ↔
    (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ)ᴴ * Jpq p q * g = Jpq p q := by sorry
