-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_det_X_ne_zero
-- name    : GlobalTheory.MinorNorm.det_X_ne_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:43.284335+00:00
-- url     : https://prove2.me/theorems/5962d0c6-ccbc-4111-8d82-d9d2291fd021
-- title:
--   Minor Norm: det X ne zero
-- statement:
--   The Minor Norm construction uses the det X ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L521-L540
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L521-L540

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
variable {σ : Type}

theorem GlobalTheory.MinorNorm.det_X_ne_zero {k : ℕ} (v : Fin k → Fin k → σ)
    (hv : ∀ r c s e, v r c = v s e → r = s ∧ c = e) :
    (Matrix.of fun r c => (X (v r c) : MvPolynomial σ ℂ)).det ≠ 0 := by sorry
