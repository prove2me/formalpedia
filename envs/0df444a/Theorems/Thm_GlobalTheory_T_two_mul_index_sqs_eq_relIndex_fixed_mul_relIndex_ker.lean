-- Prove2me | Theorems.Thm_GlobalTheory_T_two_mul_index_sqs_eq_relIndex_fixed_mul_relIndex_ker
-- name    : GlobalTheory.T.two_mul_index_sqs_eq_relIndex_fixed_mul_relIndex_ker
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T20:59:31.873848+00:00
-- url     : https://prove2.me/theorems/9c6c9df4-8d74-4d23-93fd-d8a2f1a00f45
-- title:
--   T: two mul index sqs eq rel Index fixed mul rel Index ker
-- statement:
--   The T construction uses the two mul index sqs eq rel Index fixed mul rel Index ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TwoMulIndexSqsInvolutionStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/TwoMulIndexSqsInvolutionStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoMulIndexSqsInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_TwoMulIndexSqsInvolutionStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.two_mul_index_sqs_eq_relIndex_fixed_mul_relIndex_ker : ∀ (A : Type) [CommGroup A] (σ : A →* A) (ε : A), (∀ a, σ (σ a) = a) → (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → ε ≠ 1 → ε ^ 2 = 1 → σ ε = ε → (∀ a : A, a ^ 2 = 1 → a = 1 ∨ a = ε) → 2 * (sqs (⊤ : Subgroup A)).index = (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) * (sqs (MonoidHom.id A * σ).ker).relIndex (MonoidHom.id A * σ).ker := by sorry
