-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_prod_Ioi_eq
-- name    : GlobalTheory.MinorNorm.prod_Ioi_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:27:38.731386+00:00
-- url     : https://prove2.me/theorems/665130bd-f87d-4d77-a522-c01197e00c5d
-- title:
--   Minor Norm: prod Ioi eq
-- statement:
--   The Minor Norm construction uses the prod Ioi eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L592-L604
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L592-L604

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

theorem GlobalTheory.MinorNorm.prod_Ioi_eq (K : Fin l) (g : ℕ → ℚ) :
    ∏ j ∈ Finset.Ioi K, g j = ∏ j ∈ Finset.Ico ((K : ℕ) + 1) l, g j := by sorry
