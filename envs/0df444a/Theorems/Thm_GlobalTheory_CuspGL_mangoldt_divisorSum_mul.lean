-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_mangoldt_divisorSum_mul
-- name    : GlobalTheory.CuspGL.mangoldt_divisorSum_mul
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:32:38.747491+00:00
-- url     : https://prove2.me/theorems/475ab354-21bd-4ec7-9531-cd6f2f3aedaf
-- title:
--   Cusp GL: mangoldt divisor Sum mul
-- statement:
--   The Cusp GL construction uses the mangoldt divisor Sum mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AdditiveEqPolynomialVonMangoldtConvolutionOne.lean#L55-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AdditiveEqPolynomialVonMangoldtConvolutionOne.lean#L55-L94

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

theorem GlobalTheory.CuspGL.mangoldt_divisorSum_mul (s : F[X] → ℂ) (f Q : F[X]) (hf : f.Monic) (hf' : Irreducible f)
    (hQ : Q.Monic) :
    ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ f * Q}, mangoldt s D =
      s f + ∑ᶠ D ∈ {D : F[X] | D.Monic ∧ D ∣ Q}, mangoldt s D := by sorry
