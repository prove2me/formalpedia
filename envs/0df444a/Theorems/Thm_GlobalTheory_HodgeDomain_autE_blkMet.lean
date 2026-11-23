-- Prove2me | Theorems.Thm_GlobalTheory_HodgeDomain_autE_blkMet
-- name    : GlobalTheory.HodgeDomain.autE_blkMet
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:05:31.4675+00:00
-- url     : https://prove2.me/theorems/07e59785-dbc4-4573-909e-e7c14576f452
-- title:
--   Hodge Domain: aut E blk Met
-- statement:
--   The Hodge Domain construction uses the aut E blk Met property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/HPInvEqForm.lean#L257-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/HPInvEqForm.lean#L257-L263

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

theorem GlobalTheory.HodgeDomain.autE_blkMet (g : GL (Fin p ⊕ Fin q) ℂ) (z : Matrix (Fin p) (Fin q) ℂ)
    (A : Matrix (Fin p) (Fin p) ℂ) (B : Matrix (Fin q) (Fin q) ℂ) :
    (autE g z)ᴴ * blkMet A B * autE g z =
      blkMet ((jW g z)ᴴ * A * jW g z) ((kapQ g z)ᴴ * B * kapQ g z) := by sorry
