-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_fock_int_left
-- name    : GlobalTheory.MinorNorm.fock_int_left
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:27:23.001822+00:00
-- url     : https://prove2.me/theorems/10a57744-87b7-4838-931a-3cdaf630366a
-- title:
--   Minor Norm: fock int left
-- statement:
--   The Minor Norm construction uses the fock int left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L406-L411
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L406-L411

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

theorem GlobalTheory.MinorNorm.fock_int_left (z : ℤ) (P Q : MvPolynomial σ ℂ) :
    Formalism.E.fock ((z : MvPolynomial σ ℂ) * P) Q = z * Formalism.E.fock P Q := by sorry
