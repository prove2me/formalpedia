-- Prove2me | Theorems.Thm_GlobalTheory_DiffVanish_multiDiff_form_diag
-- name    : GlobalTheory.DiffVanish.multiDiff_form_diag
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:49:16.654441+00:00
-- url     : https://prove2.me/theorems/47e318a7-60e4-4072-928e-f38a79fda1d5
-- title:
--   Diff Vanish: multi Diff form diag
-- statement:
--   The Diff Vanish construction uses the multi Diff form diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L313-L330
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L313-L330

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

theorem GlobalTheory.DiffVanish.multiDiff_form_diag {d : ℕ} {φ : G → M} (h : DiffVanish (d + 1) φ)
    (g : Fin d → G) (x : G) :
    multiDiff g (fun y ↦ h.form fun _ ↦ y) x = d.factorial • h.form g := by sorry
