-- Prove2me | Theorems.Thm_GlobalTheory_algebraMap_trace_eq_sum_points
-- name    : GlobalTheory.algebraMap_trace_eq_sum_points
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:52.042944+00:00
-- url     : https://prove2.me/theorems/e8e13214-5b4a-4767-89f3-0dfebe8389b8
-- title:
--   Global Theory: algebra Map trace eq sum points
-- statement:
--   The Global Theory construction uses the algebra Map trace eq sum points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean#L94-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean#L94-L98

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Matrix
open Module Algebra
open GlobalTheory
variable {R S : Type*} (E : Type*) [CommRing R] [CommRing S] [Algebra R S] [Field E]
  [Algebra R E] [IsFiniteSplit E (E ⊗[R] S)]
variable [Module.Free R S]
variable {E} {ι : Type*} [Fintype ι]
variable [Module.Finite R S]

theorem GlobalTheory.algebraMap_trace_eq_sum_points (P : ι ≃ (S →ₐ[R] E)) (x : S) :
    algebraMap R E (Algebra.trace R S x) = ∑ j, P j x := by sorry
