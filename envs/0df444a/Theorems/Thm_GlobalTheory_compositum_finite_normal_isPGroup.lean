-- Prove2me | Theorems.Thm_GlobalTheory_compositum_finite_normal_isPGroup
-- name    : GlobalTheory.compositum_finite_normal_isPGroup
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:44:04.583147+00:00
-- url     : https://prove2.me/theorems/3a164501-1787-5dfc-b4f8-23e362e8e192
-- title:
--   Global Theory: compositum finite normal is PGroup
-- statement:
--   The Global Theory construction uses the compositum finite normal is PGroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/CompositumFiniteNormalIsPGroup.lean#L7-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/CompositumFiniteNormalIsPGroup.lean#L7-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_CompositumFiniteNormalIsPGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open IntermediateField Polynomial

theorem GlobalTheory.compositum_finite_normal_isPGroup (K K' Ω : Type) [Field K] [Field K'] [Field Ω]
    [Algebra K K'] [Algebra K' Ω] [Algebra K Ω] [IsScalarTower K K' Ω] (l : ℕ)
    (L : IntermediateField K Ω) (hfin : FiniteDimensional K L) (hn : Normal K L)
    (hp : IsPGroup l (L ≃ₐ[K] L)) :
    FiniteDimensional K' (IntermediateField.adjoin K' (L : Set Ω)) ∧
      Normal K' (IntermediateField.adjoin K' (L : Set Ω)) ∧
      IsPGroup l (IntermediateField.adjoin K' (L : Set Ω) ≃ₐ[K']
        IntermediateField.adjoin K' (L : Set Ω)) := by sorry
