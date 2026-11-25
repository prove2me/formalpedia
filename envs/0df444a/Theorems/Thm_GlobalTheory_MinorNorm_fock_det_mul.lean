-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_fock_det_mul
-- name    : GlobalTheory.MinorNorm.fock_det_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:37.089668+00:00
-- url     : https://prove2.me/theorems/6a4e8bb0-2985-474d-8733-79923a990517
-- title:
--   Minor Norm: fock det mul
-- statement:
--   The Minor Norm construction uses the fock det mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L490-L519
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L490-L519

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

theorem GlobalTheory.MinorNorm.fock_det_mul {k : ℕ} (v : Fin k → Fin k → σ)
    (hv : ∀ r c s e, v r c = v s e → r = s ∧ c = e) (a : Fin k → ℕ) (P' P : MvPolynomial σ ℂ)
    (hP : P = (Matrix.of fun r c => (X (v r c) : MvPolynomial σ ℂ)).det * P')
    (hdet : (Matrix.of fun r c => (X (v r c) : MvPolynomial σ ℂ)).det ≠ 0)
    (hup : ∀ i j, i < j → pol (fun r c => X (v r c)) (fun r c => pderiv (v r c)) i j P = 0)
    (hwt : ∀ j, pol (fun r c => X (v r c)) (fun r c => pderiv (v r c)) j j P = a j * P) :
    Formalism.E.fock P P = ((∏ t, (a t + (k - (t + 1))) : ℕ) : ℂ) * Formalism.E.fock P' P' := by sorry
