-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_fock_sum_right
-- name    : GlobalTheory.MinorNorm.fock_sum_right
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:46.19448+00:00
-- url     : https://prove2.me/theorems/eb2941eb-5c91-4e96-8b93-c5991bd91d50
-- title:
--   Minor Norm: fock sum right
-- statement:
--   The Minor Norm construction uses the fock sum right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L399-L404
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L399-L404

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

theorem GlobalTheory.MinorNorm.fock_sum_right {ι : Type} (s : Finset ι) (P : MvPolynomial σ ℂ) (Q : ι → MvPolynomial σ ℂ) :
    Formalism.E.fock P (∑ i ∈ s, Q i) = ∑ i ∈ s, Formalism.E.fock P (Q i) := by sorry
