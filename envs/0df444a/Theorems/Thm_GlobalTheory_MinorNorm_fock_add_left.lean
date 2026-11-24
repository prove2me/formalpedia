-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_fock_add_left
-- name    : GlobalTheory.MinorNorm.fock_add_left
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:27:09.563874+00:00
-- url     : https://prove2.me/theorems/dbac44bf-1bcc-4411-9a6b-0c37c90bcefc
-- title:
--   Minor Norm: fock add left
-- statement:
--   The Minor Norm construction uses the fock add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L383-L390
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L383-L390

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

theorem GlobalTheory.MinorNorm.fock_add_left (P P' Q : MvPolynomial σ ℂ) :
    Formalism.E.fock (P + P') Q = Formalism.E.fock P Q + Formalism.E.fock P' Q := by sorry
