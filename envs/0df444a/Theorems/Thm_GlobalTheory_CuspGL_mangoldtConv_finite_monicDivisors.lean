-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_mangoldtConv_finite_monicDivisors
-- name    : GlobalTheory.CuspGL.mangoldtConv_finite_monicDivisors
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:32:45.14288+00:00
-- url     : https://prove2.me/theorems/623119a7-497d-478b-a266-021f1b1b55b6
-- title:
--   Cusp GL: mangoldt Conv finite monic Divisors
-- statement:
--   The Cusp GL construction uses the mangoldt Conv finite monic Divisors property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AdditiveEqPolynomialVonMangoldtConvolutionOne.lean#L50-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AdditiveEqPolynomialVonMangoldtConvolutionOne.lean#L50-L53

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

theorem GlobalTheory.CuspGL.mangoldtConv_finite_monicDivisors (P : F[X]) (hP : P.Monic) :
    {D : F[X] | D.Monic ∧ D ∣ P}.Finite := by sorry
