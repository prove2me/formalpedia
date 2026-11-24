-- Prove2me | Theorems.Thm_GlobalTheory_many_independent_products_in_function_field
-- name    : GlobalTheory.many_independent_products_in_function_field
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:10:07.709771+00:00
-- url     : https://prove2.me/theorems/e44f91b3-1019-45fa-b316-96e2428f41cd
-- title:
--   Global Theory: many independent products in function field
-- statement:
--   The Global Theory construction uses the many independent products in function field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ManyIndependentProductsInFunctionField.lean#L23-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ManyIndependentProductsInFunctionField.lean#L23-L96

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinRootMapComplexLinearIndependentStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormalBranchesOfSeparableReductionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveMonicSeparableSpecializationStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankMulPowLeFinrankOfPowerSeriesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ManyIndependentProductsInFunctionField
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory

theorem GlobalTheory.many_independent_products_in_function_field : ∀ (K : Type) [Field K] [CharZero K] (D : ℕ)
    (x : Fin D → K), IsTranscendenceBasis ℤ x → ∀ (J : Type) [Fintype J] (e : J → K),
    LinearIndependent ℤ e → ∀ m : ℕ, 0 < m → ∃ v : Fin (Fintype.card J * m ^ D) → K,
    LinearIndependent ℤ v ∧ ∀ s, ∃ (u : Fin m → J) (a : Fin D → ℕ), (∀ i, a i < m) ∧
      v s = (∏ l, e (u l)) * ∏ i, x i ^ a i := by sorry
