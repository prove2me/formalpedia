-- Prove2me | Theorems.Thm_GlobalTheory_DiffVanish_multiDiff_eq_zero
-- name    : GlobalTheory.DiffVanish.multiDiff_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:49:20.904803+00:00
-- url     : https://prove2.me/theorems/962a2d1a-1dde-465f-92bc-bfc3d3b2ac72
-- title:
--   Diff Vanish: multi Diff eq zero
-- statement:
--   The Diff Vanish construction uses the multi Diff eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L177-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L177-L180

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

theorem GlobalTheory.DiffVanish.multiDiff_eq_zero {n : ℕ} {φ : G → M} (h : DiffVanish n φ)
    {ι : Type*} [Fintype ι] (hn : n ≤ Fintype.card ι) (g : ι → G) : multiDiff g φ = 0 := by sorry
