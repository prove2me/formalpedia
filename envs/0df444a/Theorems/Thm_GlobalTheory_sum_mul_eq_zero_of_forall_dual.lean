-- Prove2me | Theorems.Thm_GlobalTheory_sum_mul_eq_zero_of_forall_dual
-- name    : GlobalTheory.sum_mul_eq_zero_of_forall_dual
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:23:12.682565+00:00
-- url     : https://prove2.me/theorems/c33f2832-d752-47ed-80ac-4f56fccc1806
-- title:
--   Global Theory: sum mul eq zero of forall dual
-- statement:
--   The Global Theory construction uses the sum mul eq zero of forall dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsCompleteDiscreteValuationRingOfMemClosureCones.lean#L7-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsCompleteDiscreteValuationRingOfMemClosureCones.lean#L7-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDiscreteValuationRingOfMemClosureC
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsCompleteDiscreteValuationRingOfMemClosureCones
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators TensorProduct
open GlobalTheory

theorem GlobalTheory.sum_mul_eq_zero_of_forall_dual {F K σ : Type} [Field F] [Field K] [Algebra F K]
    (S : Finset σ) (c m : σ → K)
    (h : ∀ l : K →ₗ[F] F, ∑ s ∈ S, l (c s) • m s = 0) : ∑ s ∈ S, c s * m s = 0 := by sorry
