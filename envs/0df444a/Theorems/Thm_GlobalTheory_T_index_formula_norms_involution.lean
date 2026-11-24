-- Prove2me | Theorems.Thm_GlobalTheory_T_index_formula_norms_involution
-- name    : GlobalTheory.T.index_formula_norms_involution
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T20:46:48.46035+00:00
-- url     : https://prove2.me/theorems/8b81a9f1-4278-4ae1-b3ca-ff4d24ded98c
-- title:
--   T: index formula norms involution
-- statement:
--   The T construction uses the index formula norms involution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexFormulaNormsInvolutionStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IndexFormulaNormsInvolutionStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexFormulaNormsInvolution
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IndexFormulaNormsInvolutionStatement
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

theorem GlobalTheory.T.index_formula_norms_involution : ∀ (A : Type) [CommGroup A] (σ : A →* A) (ε : A), (∀ a, σ (σ a) = a) → (∀ a, a * σ a = 1 → ∃ b, a = b / σ b) → ε ≠ 1 → ε ^ 2 = 1 → σ ε = ε → (∀ a : A, a ^ 2 = 1 → a = 1 ∨ a = ε) → 2 * (sqs (⊤ : Subgroup A)).index * (MonoidHom.id A * σ).range.relIndex (σ.eqLocus (MonoidHom.id A)) = (sqs (σ.eqLocus (MonoidHom.id A))).relIndex (σ.eqLocus (MonoidHom.id A)) ^ 2 := by sorry
