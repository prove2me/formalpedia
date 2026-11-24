-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_hookProd_addCol
-- name    : GlobalTheory.MinorNorm.hookProd_addCol
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:18.580853+00:00
-- url     : https://prove2.me/theorems/b8129166-83b8-4f40-b586-167d307bb9e2
-- title:
--   Minor Norm: hook Prod add Col
-- statement:
--   The Minor Norm construction uses the hook Prod add Col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L640-L699
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L640-L699

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

theorem GlobalTheory.MinorNorm.hookProd_addCol {a : Fin l → ℕ} (ha : Antitone a) (K : Fin l) (hK : ∀ i, K < i → a i = 0) :
    hookProd (addCol a K) =
      (∏ i : Fin l, if i ≤ K then ((a i : ℚ) + 1 + (K : ℕ) - (i : ℕ)) else 1) * hookProd a := by sorry
