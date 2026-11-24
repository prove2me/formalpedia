-- Prove2me | Theorems.Thm_GlobalTheory_DiffVanish_form_apply
-- name    : GlobalTheory.DiffVanish.form_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:59:26.225029+00:00
-- url     : https://prove2.me/theorems/fabc8cfa-1fb8-4002-baef-dcd2daed4b6c
-- title:
--   Diff Vanish: form apply
-- statement:
--   The Diff Vanish construction uses the form apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L237-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L237-L238

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

theorem GlobalTheory.DiffVanish.form_apply {d : ℕ} {φ : G → M} (h : DiffVanish (d + 1) φ) (g : Fin d → G)
    (x : G) : h.form g = multiDiff g φ x := by sorry
