-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_exponent_regular_of_natDegree_minpoly_pow
-- name    : GlobalTheory.CuspGL.exponent_regular_of_natDegree_minpoly_pow
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:32:07.727845+00:00
-- url     : https://prove2.me/theorems/260bfb89-27ff-489d-aa81-bd3cbf83d72f
-- title:
--   Cusp GL: exponent regular of nat Degree minpoly pow
-- statement:
--   The Cusp GL construction uses the exponent regular of nat Degree minpoly pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExponentRegularOfNatDegreeMinpolyGeneratorPow.lean#L8-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/ExponentRegularOfNatDegreeMinpolyGeneratorPow.lean#L8-L20

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_AbByPOfComm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_ExponentRegularOfNatDegreeMinpolyGeneratorPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI
open GlobalTheory GlobalTheory.CuspGL

theorem GlobalTheory.CuspGL.exponent_regular_of_natDegree_minpoly_pow : ∀ (F : Type) [Field F] [Finite F] (d k : ℕ) (ζ : AlgebraicClosure F), 0 < d → orderOf ζ = Nat.card F ^ d - 1 → (minpoly F (ζ ^ k)).natDegree = d → ∀ i : ℕ, 0 < i → i < d → ¬ k * Nat.card F ^ i ≡ k [MOD Nat.card F ^ d - 1] := by sorry
