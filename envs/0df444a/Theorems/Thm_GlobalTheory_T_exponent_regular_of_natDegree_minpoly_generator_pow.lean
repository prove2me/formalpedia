-- Prove2me | Theorems.Thm_GlobalTheory_T_exponent_regular_of_natDegree_minpoly_generator_pow
-- name    : GlobalTheory.T.exponent_regular_of_natDegree_minpoly_generator_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:54:41.481241+00:00
-- url     : https://prove2.me/theorems/68fbd93e-4cfe-4a85-a553-46cce31fc77a
-- title:
--   T: exponent regular of nat Degree minpoly generator pow
-- statement:
--   The T construction uses the exponent regular of nat Degree minpoly generator pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExponentRegularOfNatDegreeMinpolyGeneratorPowStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExponentRegularOfNatDegreeMinpolyGeneratorPowStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExponentRegularOfNatDegreeMinpolyGeneratorPow
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExponentRegularOfNatDegreeMinpolyGeneratorPowStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exponent_regular_of_natDegree_minpoly_generator_pow : ∀ (F : Type) [Field F] [Finite F] (d k : ℕ) (ζ : AlgebraicClosure F), 0 < d → orderOf ζ = Nat.card F ^ d - 1 → (minpoly F (ζ ^ k)).natDegree = d → ∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1] := by sorry
