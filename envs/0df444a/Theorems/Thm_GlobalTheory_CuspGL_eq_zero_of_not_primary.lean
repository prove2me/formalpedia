-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_eq_zero_of_not_primary
-- name    : GlobalTheory.CuspGL.eq_zero_of_not_primary
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:30:48.066189+00:00
-- url     : https://prove2.me/theorems/68247e00-0368-476c-907e-2d9cfc2f49f7
-- title:
--   Cusp GL: eq zero of not primary
-- statement:
--   The Cusp GL construction uses the eq zero of not primary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EqZeroOfNotPrimary.lean#L33-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EqZeroOfNotPrimary.lean#L33-L123

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExistsConjEqAddOfIsCoprime
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
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

theorem GlobalTheory.CuspGL.eq_zero_of_not_primary : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → 0 < Module.finrank F V →
    ∀ g : Module.End F V, (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧
      LinearMap.charpoly g = f ^ m) → φ g = 0 := by sorry
