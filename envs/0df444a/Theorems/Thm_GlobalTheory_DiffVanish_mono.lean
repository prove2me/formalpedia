-- Prove2me | Theorems.Thm_GlobalTheory_DiffVanish_mono
-- name    : GlobalTheory.DiffVanish.mono
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:04:12.772805+00:00
-- url     : https://prove2.me/theorems/7ef26bf7-4618-4638-958f-4e65697fec7d
-- title:
--   Diff Vanish: mono
-- statement:
--   The Diff Vanish construction uses the mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L182-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsMvPolynomialOfIteratedBackwardDifferenceVa.lean#L182-L183

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

theorem GlobalTheory.DiffVanish.mono {m n : ℕ} {φ : G → M} (h : DiffVanish m φ) (hmn : m ≤ n) :
    DiffVanish n φ := by sorry
