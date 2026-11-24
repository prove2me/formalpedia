-- Prove2me | Theorems.Thm_GlobalTheory_T_classFn_eq_zero_of_charpoly_not_irreducible_pow
-- name    : GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:20:35.278281+00:00
-- url     : https://prove2.me/theorems/f99cecf0-7ad2-4942-b194-dbb8e414a373
-- title:
--   T: class Fn eq zero of charpoly not irreducible pow
-- statement:
--   The T construction uses the class Fn eq zero of charpoly not irreducible pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EqZeroOfNotPrimaryStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/EqZeroOfNotPrimaryStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimary
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_EqZeroOfNotPrimaryStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.classFn_eq_zero_of_charpoly_not_irreducible_pow : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V] (φ : Module.End F V → ℂ), IsClassFn φ → IsPrimitive φ → 0 < Module.finrank F V → ∀ g : Module.End F V, (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ LinearMap.charpoly g = f ^ m) → φ g = 0 := by sorry
