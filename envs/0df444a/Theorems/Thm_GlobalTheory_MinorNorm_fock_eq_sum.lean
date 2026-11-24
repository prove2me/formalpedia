-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_fock_eq_sum
-- name    : GlobalTheory.MinorNorm.fock_eq_sum
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:27:38.897146+00:00
-- url     : https://prove2.me/theorems/ed9b8342-0b9a-48b1-a66b-e0f464366da7
-- title:
--   Minor Norm: fock eq sum
-- statement:
--   The Minor Norm construction uses the fock eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L377-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L377-L381

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

theorem GlobalTheory.MinorNorm.fock_eq_sum (P Q : MvPolynomial σ ℂ) (s : Finset (σ →₀ ℕ)) (hs : P.support ⊆ s) :
    Formalism.E.fock P Q = ∑ m ∈ s, P.coeff m * star (Q.coeff m) * (Formalism.A.mfact m : ℂ) := by sorry
