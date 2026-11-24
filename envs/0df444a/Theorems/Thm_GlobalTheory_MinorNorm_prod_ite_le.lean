-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_prod_ite_le
-- name    : GlobalTheory.MinorNorm.prod_ite_le
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:28:23.588057+00:00
-- url     : https://prove2.me/theorems/6a7deebc-06db-4e99-8ca7-00d1374e4546
-- title:
--   Minor Norm: prod ite le
-- statement:
--   The Minor Norm construction uses the prod ite le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L701-L717
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L701-L717

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

theorem GlobalTheory.MinorNorm.prod_ite_le (K : Fin l) (g : Fin l → ℚ) :
    (∏ i : Fin l, if i ≤ K then g i else 1) =
      ∏ t : Fin (K + 1), g (Fin.castLE K.2 t) := by sorry
