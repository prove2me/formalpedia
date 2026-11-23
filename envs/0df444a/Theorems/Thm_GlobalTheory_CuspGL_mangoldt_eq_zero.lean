-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_mangoldt_eq_zero
-- name    : GlobalTheory.CuspGL.mangoldt_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:58.308544+00:00
-- url     : https://prove2.me/theorems/d6fcd84e-d944-41cc-bfa3-07a638fbf8a2
-- title:
--   Cusp GL: mangoldt eq zero
-- statement:
--   The Cusp GL construction uses the mangoldt eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AdditiveEqPolynomialVonMangoldtConvolutionOne.lean#L26-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AdditiveEqPolynomialVonMangoldtConvolutionOne.lean#L26-L33

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveEqPolynomialVonMangoldtConvolutionOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F]

theorem GlobalTheory.CuspGL.mangoldt_eq_zero (s : F[X] → ℂ) (P : F[X])
    (h : ¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) : mangoldt s P = 0 := by sorry
