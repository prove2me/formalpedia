-- Prove2me | Theorems.Thm_GlobalTheory_T_nonempty_adjoin_algHom_of_mul_mem_of_map_ne_zero
-- name    : GlobalTheory.T.nonempty_adjoin_algHom_of_mul_mem_of_map_ne_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T20:53:56.087818+00:00
-- url     : https://prove2.me/theorems/fd280773-6da8-4d22-8e4c-6a23bbaba39f
-- title:
--   T: nonempty adjoin alg Hom of mul mem of map ne zero
-- statement:
--   The T construction uses the nonempty adjoin alg Hom of mul mem of map ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdjoinHomExtendOfDenominatorStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/AdjoinHomExtendOfDenominatorStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinHomExtendOfDenominator
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AdjoinHomExtendOfDenominatorStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.nonempty_adjoin_algHom_of_mul_mem_of_map_ne_zero : ∀ (k F Ω : Type) [Field k] [Field F] [Algebra k F] [Field Ω] [Algebra k Ω] (S : Subalgebra k F) (ψ : S →ₐ[k] Ω) (h : S), ψ h ≠ 0 → ∀ T : Set F, (∀ x ∈ T, (h : F) * x ∈ S) → Nonempty (Algebra.adjoin k T →ₐ[k] Ω) := by sorry
