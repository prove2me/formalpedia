-- Prove2me | Theorems.Thm_GlobalTheory_ExactSeq_sum_neg_one_pow_finrank_eq_zero
-- name    : GlobalTheory.ExactSeq.sum_neg_one_pow_finrank_eq_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:05:04.395439+00:00
-- url     : https://prove2.me/theorems/1369e822-877d-4d11-bd62-bfa14ab30d44
-- title:
--   Exact Seq: sum neg one pow finrank eq zero
-- statement:
--   The Exact Seq construction uses the sum neg one pow finrank eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L63-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L63-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Module
universe t v u
noncomputable section
open GlobalTheory
open GlobalTheory.ExactSeq
variable {k : Type*} [DivisionRing k]

theorem GlobalTheory.ExactSeq.sum_neg_one_pow_finrank_eq_zero {V : ℕ → Type*} [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] (f : ∀ i, V i →ₗ[k] V (i + 1)) (N : ℕ)
    (hV : ∀ i < N, Module.Finite k (V i)) (h₀ : Function.Injective (f 0))
    (h : ∀ i < N, Function.Exact (f i) (f (i + 1))) (hN : Subsingleton (V N)) :
    ∑ i ∈ Finset.range N, (-1 : ℤ) ^ i * finrank k (V i) = 0 := by sorry
