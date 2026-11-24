-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_telescope
-- name    : GlobalTheory.MinorNorm.telescope
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:28:27.338425+00:00
-- url     : https://prove2.me/theorems/b801b4e8-648f-4ff7-9886-ce109f79451d
-- title:
--   Minor Norm: telescope
-- statement:
--   The Minor Norm construction uses the telescope property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L606-L613
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L606-L613

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_BottomMinor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_PolarisationOperatorApplyVariable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix Finset
noncomputable section
open GlobalTheory GlobalTheory.MinorNorm
open GlobalTheory.IndefiniteRowSideFullHecke.CornerMinors
variable {l : ℕ}

theorem GlobalTheory.MinorNorm.telescope (c : ℚ) (s t : ℕ) (h : s ≤ t) :
    (∏ j ∈ Finset.Ico s t, (c + 1 + j)) * (c + s) = (∏ j ∈ Finset.Ico s t, (c + j)) * (c + t) := by sorry
