-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_prod_sub_eq_factorial
-- name    : GlobalTheory.MinorNorm.prod_sub_eq_factorial
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:28:35.954863+00:00
-- url     : https://prove2.me/theorems/bd206e5f-cd92-468c-a2ff-f17f2c27290b
-- title:
--   Minor Norm: prod sub eq factorial
-- statement:
--   The Minor Norm construction uses the prod sub eq factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L615-L622
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L615-L622

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

theorem GlobalTheory.MinorNorm.prod_sub_eq_factorial (s t : ℕ) (h : s + 1 ≤ t) :
    ∏ j ∈ Finset.Ico (s + 1) t, ((j : ℚ) - s) = (t - (s + 1)).factorial := by sorry
