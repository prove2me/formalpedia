-- Prove2me | Theorems.Thm_GlobalTheory_fg_of_integral_functionals
-- name    : GlobalTheory.fg_of_integral_functionals
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:48.637214+00:00
-- url     : https://prove2.me/theorems/8851bd7f-08f3-5d07-ac13-b6fcb187fa60
-- title:
--   Global Theory: fg of integral functionals
-- statement:
--   The Global Theory construction uses the fg of integral functionals property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FgIntOfForallIsIntegral.lean#L15-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FgIntOfForallIsIntegral.lean#L15-L51

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FgIntOfForallIsIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open GlobalTheory

theorem GlobalTheory.fg_of_integral_functionals (K : Type) [Field K] [NumberField K] (C : Type)
    [AddCommGroup C] [Module K C] [FiniteDimensional K C] [Module (𝓞 K) C]
    [IsScalarTower (𝓞 K) K C] (L : Submodule (𝓞 K) C)
    (h : ∀ x : C, x ≠ 0 → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K')
      (φ : C →ₗ[K] K'), φ x ≠ 0 ∧ ∀ y ∈ L, IsIntegral ℤ (φ y)) : L.FG := by sorry
