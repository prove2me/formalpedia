-- Prove2me | Theorems.Thm_GlobalTheory_DiffVanish_multiDiff_eq
-- name    : GlobalTheory.DiffVanish.multiDiff_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:49:04.981138+00:00
-- url     : https://prove2.me/theorems/4f9de899-9b77-48d5-84f1-b52b727a602d
-- title:
--   Diff Vanish: multi Diff eq
-- statement:
--   The Diff Vanish construction uses the multi Diff eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L205-L209
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L205-L209

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

theorem GlobalTheory.DiffVanish.multiDiff_eq {d : ℕ} {φ : G → M} (h : DiffVanish (d + 1) φ) (g : Fin d → G)
    (x y : G) : multiDiff g φ x = multiDiff g φ y := by sorry
