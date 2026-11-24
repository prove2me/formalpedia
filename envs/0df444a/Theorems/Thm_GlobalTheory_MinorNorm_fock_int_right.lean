-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_fock_int_right
-- name    : GlobalTheory.MinorNorm.fock_int_right
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:27:38.498945+00:00
-- url     : https://prove2.me/theorems/6a9e345b-2b0c-434a-aea0-105527cc429e
-- title:
--   Minor Norm: fock int right
-- statement:
--   The Minor Norm construction uses the fock int right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L413-L418
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L413-L418

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

theorem GlobalTheory.MinorNorm.fock_int_right (z : ℤ) (P Q : MvPolynomial σ ℂ) :
    Formalism.E.fock P ((z : MvPolynomial σ ℂ) * Q) = z * Formalism.E.fock P Q := by sorry
