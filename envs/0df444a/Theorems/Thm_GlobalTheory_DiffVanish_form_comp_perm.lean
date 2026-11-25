-- Prove2me | Theorems.Thm_GlobalTheory_DiffVanish_form_comp_perm
-- name    : GlobalTheory.DiffVanish.form_comp_perm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:04:15.32935+00:00
-- url     : https://prove2.me/theorems/196d3b7f-a664-44b1-bbfb-291750b4fdbe
-- title:
--   Diff Vanish: form comp perm
-- statement:
--   The Diff Vanish construction uses the form comp perm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L240-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L240-L242

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsMvPolynomialOfIteratedBackwardDifferenceVa
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Finset
variable {G M : Type*} [AddCommGroup G] [AddCommGroup M]

theorem GlobalTheory.DiffVanish.form_comp_perm {d : ℕ} {φ : G → M} (h : DiffVanish (d + 1) φ)
    (g : Fin d → G) (σ : Equiv.Perm (Fin d)) : h.form (g ∘ σ) = h.form g := by sorry
