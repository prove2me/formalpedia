-- Prove2me | Theorems.Thm_GlobalTheory_DiffVanish_sub_form_diag
-- name    : GlobalTheory.DiffVanish.sub_form_diag
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:49:29.302236+00:00
-- url     : https://prove2.me/theorems/03b340df-ff79-483d-81ff-f5bde94a9cfd
-- title:
--   Diff Vanish: sub form diag
-- statement:
--   The Diff Vanish construction uses the sub form diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L338-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L338-L346

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
variable {G K : Type*} [AddCommGroup G] [Field K] [CharZero K]

theorem GlobalTheory.DiffVanish.sub_form_diag {d : ℕ} {φ : G → K} (h : DiffVanish (d + 1) φ) :
    DiffVanish d (φ - fun y ↦ (d.factorial : K)⁻¹ * h.form fun _ ↦ y) := by sorry
