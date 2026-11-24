-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_del_addCol
-- name    : GlobalTheory.MinorNorm.del_addCol
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:27:58.350513+00:00
-- url     : https://prove2.me/theorems/e9a63fdc-3a70-496d-b845-19e32f933665
-- title:
--   Minor Norm: del add Col
-- statement:
--   The Minor Norm construction uses the del add Col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L728-L733
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L728-L733

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
variable {σ : Type} (v : Fin l → Fin l → σ)

theorem GlobalTheory.MinorNorm.del_addCol {a : Fin l → ℕ} (ha : Antitone a) (K : Fin l) :
    del v (addCol a K) = minor v K * del v a := by sorry
