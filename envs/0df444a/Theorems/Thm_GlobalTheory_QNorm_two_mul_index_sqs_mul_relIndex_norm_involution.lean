-- Prove2me | Theorems.Thm_GlobalTheory_QNorm_two_mul_index_sqs_mul_relIndex_norm_involution
-- name    : GlobalTheory.QNorm.two_mul_index_sqs_mul_relIndex_norm_involution
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:03:24.118452+00:00
-- url     : https://prove2.me/theorems/e27e4470-6ff7-4d70-a782-8dee587c2f51
-- title:
--   QNorm: two mul index sqs mul rel Index norm involution
-- statement:
--   The QNorm construction uses the two mul index sqs mul rel Index norm involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexFormulaNormsInvolution.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexFormulaNormsInvolution.lean#L10-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_RelIndexNormMulRelIndexSqsKerStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoMulIndexSqsInvolutionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexFormulaNormsInvolution
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.QNorm
open scoped WithZero
open GlobalTheory GlobalTheory.QNorm

theorem GlobalTheory.QNorm.two_mul_index_sqs_mul_relIndex_norm_involution :
    ∀ (A : Type) [CommGroup A] (σ : A →* A) (ε : A), (∀ a, σ (σ a) = a) → (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → ε ≠ 1 → ε ^ 2 = 1 → σ ε = ε → (∀ a : A, a ^ 2 = 1 → a = 1 ∨ a = ε) → 2 * (sqs (⊤ : Subgroup A)).index * (MonoidHom.id A * σ).range.relIndex (σ.eqLocus (MonoidHom.id A)) = (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) ^ 2 := by sorry
