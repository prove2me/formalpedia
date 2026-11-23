-- Prove2me | Theorems.Thm_GlobalTheory_HodgeDomain_kapQ_gram
-- name    : GlobalTheory.HodgeDomain.kapQ_gram
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:02:34.908103+00:00
-- url     : https://prove2.me/theorems/5bb68bf1-e3e6-42c3-9785-517ff3174309
-- title:
--   Hodge Domain: kap Q gram
-- statement:
--   The Hodge Domain construction uses the kap Q gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/HPInvEqForm.lean#L73-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AutomorphicMembership/HPInvEqForm.lean#L73-L89

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

theorem GlobalTheory.HodgeDomain.kapQ_gram {g : GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ Upq p q) (z : Matrix (Fin p) (Fin q) ℂ) :
    (kapQ g z)ᴴ * kapQ g z -
      ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ * z +
        (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂)ᴴ *
      ((g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₁ * z +
        (g : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ).toBlocks₁₂) = hQ z := by sorry
