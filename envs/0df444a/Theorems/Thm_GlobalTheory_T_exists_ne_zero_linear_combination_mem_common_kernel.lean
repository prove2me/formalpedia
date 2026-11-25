-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_ne_zero_linear_combination_mem_common_kernel
-- name    : GlobalTheory.T.exists_ne_zero_linear_combination_mem_common_kernel
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:30:23.289835+00:00
-- url     : https://prove2.me/theorems/6a004f53-cb4d-5cb9-8ddf-d1ac42efcc19
-- title:
--   T: exists ne zero linear combination mem common kernel
-- statement:
--   The T construction uses the exists ne zero linear combination mem common kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroLinearCombinationMemCommonKernelStatement.lean#L9-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsNeZeroLinearCombinationMemCommonKernelStatement.lean#L9-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroLinearCombinationMemCommonKernel
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsAdmissibleIntegralBasisChangeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsNeZeroLinearCombinationMemCommonKernelStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Nef
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_ne_zero_linear_combination_mem_common_kernel : ∀ (k F ι : Type) [Field k] [Field F] [Algebra k F] (n m : ℕ) (f : Fin m → F),
  LinearIndependent k f → ∀ (S : Finset ι) (N : ι → ℕ) (ψ : ∀ v, (Fin n → F) →ₗ[k] (Fin (N v) → k)),
    ∑ v ∈ S, N v < n * m → ∃ c : Fin n → Fin m → k, (fun i => ∑ j, c i j • f j) ≠ 0 ∧
      ∀ v ∈ S, ψ v (fun i => ∑ j, c i j • f j) = 0 := by sorry
