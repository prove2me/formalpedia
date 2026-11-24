-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_addCol_antitone
-- name    : GlobalTheory.MinorNorm.addCol_antitone
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:28:10.237979+00:00
-- url     : https://prove2.me/theorems/c0ac3449-7213-42dc-a915-e1efd127218a
-- title:
--   Minor Norm: add Col antitone
-- statement:
--   The Minor Norm construction uses the add Col antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L632-L638
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L632-L638

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

theorem GlobalTheory.MinorNorm.addCol_antitone {a : Fin l → ℕ} (ha : Antitone a) (K : Fin l) : Antitone (addCol a K) := by sorry
