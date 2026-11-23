-- Prove2me | Theorems.Thm_GlobalTheory_T_additive_eq_polynomialVonMangoldt_convolution_one
-- name    : GlobalTheory.T.additive_eq_polynomialVonMangoldt_convolution_one
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T04:17:49.065422+00:00
-- url     : https://prove2.me/theorems/a0cfc7ac-c57d-4186-b387-8fd2a949cbdb
-- title:
--   T: additive eq polynomial Von Mangoldt convolution one
-- statement:
--   The T construction uses the additive eq polynomial Von Mangoldt convolution one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AdditiveEqPolynomialVonMangoldtConvolutionOneStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AdditiveEqPolynomialVonMangoldtConvolutionOneStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOne
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOneStatement
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

theorem GlobalTheory.T.additive_eq_polynomialVonMangoldt_convolution_one : ∀ (F : Type) [Field F] (s : F[X] → ℂ), IsAdditive s → (∀ P : F[X], P.Monic → s P = conv (mangoldt s) (fun _ => 1) P) ∧ (∀ (f : F[X]) (m : ℕ), f.Monic → Irreducible f → 0 < m → mangoldt s (f ^ m) = s f) ∧ ∀ P : F[X], (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) → mangoldt s P = 0 := by sorry
