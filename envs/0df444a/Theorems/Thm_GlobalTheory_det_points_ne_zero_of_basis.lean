-- Prove2me | Theorems.Thm_GlobalTheory_det_points_ne_zero_of_basis
-- name    : GlobalTheory.det_points_ne_zero_of_basis
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:15:43.810596+00:00
-- url     : https://prove2.me/theorems/6ff74579-3781-47b7-b333-6550bdbff56a
-- title:
--   Global Theory: det points ne zero of basis
-- statement:
--   The Global Theory construction uses the det points ne zero of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean#L112-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean#L112-L119

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
omit [Module.Free R S] [Module.Finite R S]

theorem GlobalTheory.det_points_ne_zero_of_basis (P : ι ≃ (S →ₐ[R] E)) (b : Basis ι R S) :
    (Matrix.of fun i j ↦ P j (b i)).det ≠ 0 := by sorry
