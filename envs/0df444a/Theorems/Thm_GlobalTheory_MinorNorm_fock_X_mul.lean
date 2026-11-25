-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_fock_X_mul
-- name    : GlobalTheory.MinorNorm.fock_X_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:43.389716+00:00
-- url     : https://prove2.me/theorems/afa91573-cb89-48d1-8101-ef5be61f0b61
-- title:
--   Minor Norm: fock X mul
-- statement:
--   The Minor Norm construction uses the fock X mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L462-L474
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L462-L474

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

theorem GlobalTheory.MinorNorm.fock_X_mul (v : σ) (P Q : MvPolynomial σ ℂ) :
    Formalism.E.fock (X v * P) Q = Formalism.E.fock P (pderiv v Q) := by sorry
