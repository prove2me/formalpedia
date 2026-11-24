-- Prove2me | Theorems.Thm_GlobalTheory_det_points_sq_eq_discr
-- name    : GlobalTheory.det_points_sq_eq_discr
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:11:00.520949+00:00
-- url     : https://prove2.me/theorems/ee0b9d0d-8739-4e36-a291-6c12a6e09846
-- title:
--   Global Theory: det points sq eq discr
-- statement:
--   The Global Theory construction uses the det points sq eq discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean#L102-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean#L102-L108

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
variable [DecidableEq ι]

theorem GlobalTheory.det_points_sq_eq_discr (P : ι ≃ (S →ₐ[R] E)) (v : ι → S) :
    (Matrix.of fun i j ↦ P j (v i)).det ^ 2 = algebraMap R E (discr R v) := by sorry
