-- Prove2me | Theorems.Thm_GlobalTheory_det_points_ne_zero_iff
-- name    : GlobalTheory.det_points_ne_zero_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:15:35.284899+00:00
-- url     : https://prove2.me/theorems/8655c7fc-1388-412e-8884-bfa18b0a93e0
-- title:
--   Global Theory: det points ne zero iff
-- statement:
--   The Global Theory construction uses the det points ne zero iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean#L142-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean#L142-L153

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
variable (K A : Type*) [Field K] [CommRing A] [Algebra K A]
variable {K A} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.det_points_ne_zero_iff {E : Type*} [Field E] [Algebra K E] [Module.Finite K A]
    [IsFiniteSplit E (E ⊗[K] A)] (P : ι ≃ (A →ₐ[K] E)) (v : ι → A) :
    (Matrix.of fun i j ↦ P j (v i)).det ≠ 0 ↔ LinearIndependent K v := by sorry
