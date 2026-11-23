-- Prove2me | Theorems.Thm_GlobalTheory_T_dirichletL_zeros_eq_primitiveCharacter_zeros
-- name    : GlobalTheory.T.dirichletL_zeros_eq_primitiveCharacter_zeros
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:48:24.086635+00:00
-- url     : https://prove2.me/theorems/57c8e41a-1d0a-4bb3-82e1-862b3d9d56ed
-- title:
--   T: dirichlet L zeros eq primitive Character zeros
-- statement:
--   The T construction uses the dirichlet L zeros eq primitive Character zeros property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DirichletLZerosEqPrimitiveCharacterZerosStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/DirichletLZerosEqPrimitiveCharacterZerosStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DirichletLZerosEqPrimitiveCharacterZeros
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DirichletLZerosEqPrimitiveCharacterZerosStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.dirichletL_zeros_eq_primitiveCharacter_zeros : ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), 0 < s.re → (χ ≠ 1 ∨ s ≠ 1) → haveI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩; (LFunction χ s = 0 ↔ LFunction χ.primitiveCharacter s = 0) ∧ ord χ s = ord χ.primitiveCharacter s := by sorry
