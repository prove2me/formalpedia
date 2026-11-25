-- Prove2me | Theorems.Thm_GlobalTheory_MinorNorm_fock_prod_mul
-- name    : GlobalTheory.MinorNorm.fock_prod_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:28:50.540365+00:00
-- url     : https://prove2.me/theorems/dcf310bf-59d9-4176-a708-d3edfccebd38
-- title:
--   Minor Norm: fock prod mul
-- statement:
--   The Minor Norm construction uses the fock prod mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L476-L488
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/PolarisationOperatorApplyVariable.lean#L476-L488

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

theorem GlobalTheory.MinorNorm.fock_prod_mul {k : ℕ} (v : Fin k → Fin k → σ) :
    ∀ (m : ℕ) (ρ J : Fin m → Fin k) (P Q : MvPolynomial σ ℂ),
      Formalism.E.fock ((∏ t, X (v (ρ t) (J t))) * P) Q =
        Formalism.E.fock P (iterD (fun r c => pderiv (v r c)) m ρ J Q) := by sorry
