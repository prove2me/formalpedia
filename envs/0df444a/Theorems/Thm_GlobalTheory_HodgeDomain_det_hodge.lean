-- Prove2me | Theorems.Thm_GlobalTheory_HodgeDomain_det_hodge
-- name    : GlobalTheory.HodgeDomain.det_hodge
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:37:06.563807+00:00
-- url     : https://prove2.me/theorems/57298283-eed7-462f-aabc-0bf43a501546
-- title:
--   Hodge Domain: det hodge
-- statement:
--   The Hodge Domain construction uses the det hodge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/HPInvEqForm.lean#L282-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/HPInvEqForm.lean#L282-L289

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

theorem GlobalTheory.HodgeDomain.det_hodge (c : ℝ) {z : Matrix (Fin p) (Fin q) ℂ} (hz : z ∈ hcDom p q) :
    (hodge c z).det = (c : ℂ) ^ (p + q) := by sorry
