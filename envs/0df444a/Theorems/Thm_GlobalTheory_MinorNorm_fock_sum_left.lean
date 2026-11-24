-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_fock_sum_left
-- name    : GlobalTheory.MinorNorm.fock_sum_left
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:12.17439+00:00
-- url     : https://prove2.me/theorems/6c852d73-e231-4da4-97d0-35253796717a
-- title:
--   Minor Norm: fock sum left
-- statement:
--   The Minor Norm construction uses the fock sum left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L392-L397
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L392-L397

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

theorem GlobalTheory.MinorNorm.fock_sum_left {ι : Type} (s : Finset ι) (P : ι → MvPolynomial σ ℂ) (Q : MvPolynomial σ ℂ) :
    Formalism.E.fock (∑ i ∈ s, P i) Q = ∑ i ∈ s, Formalism.E.fock (P i) Q := by sorry
