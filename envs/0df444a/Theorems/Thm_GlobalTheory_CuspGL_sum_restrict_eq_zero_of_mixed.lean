-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_sum_restrict_eq_zero_of_mixed
-- name    : GlobalTheory.CuspGL.sum_restrict_eq_zero_of_mixed
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T12:34:28.519845+00:00
-- url     : https://prove2.me/theorems/06c2938a-a127-43e4-80bb-975d49b58f0b
-- title:
--   Cusp GL: sum restrict eq zero of mixed
-- statement:
--   The Cusp GL construction uses the sum restrict eq zero of mixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SumPrimitiveEndClassFunctionRestrictMixedSubspac.lean#L34-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/SumPrimitiveEndClassFunctionRestrictMixedSubspac.lean#L34-L97

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_SumPrimitiveEndClassFunctionRestrictMixedSubspac
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.sum_restrict_eq_zero_of_mixed (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (A W : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A)
    (h1 : W ⊓ A ≠ ⊥) (h2 : ¬ W ≤ A) (φ : Module.End F W → ℂ) (hφ : IsPrimitive φ) :
    ∑ᶠ h : {h : Module.End F V // h ∈ nilRad A ∧ ∀ x ∈ W, (g + h) x ∈ W},
      φ ((g + h.1).restrict h.2.2) = 0 := by sorry
