-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_mangoldt_pow
-- name    : GlobalTheory.CuspGL.mangoldt_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:33:20.516359+00:00
-- url     : https://prove2.me/theorems/b427482c-5c7b-49fb-bfee-d135887e30c2
-- title:
--   Cusp GL: mangoldt pow
-- statement:
--   The Cusp GL construction uses the mangoldt pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AdditiveEqPolynomialVonMangoldtConvolutionOne.lean#L14-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AdditiveEqPolynomialVonMangoldtConvolutionOne.lean#L14-L24

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

theorem GlobalTheory.CuspGL.mangoldt_pow (s : F[X] → ℂ) (f : F[X]) (m : ℕ) (hf : f.Monic) (hf' : Irreducible f) (hm : 0 < m) :
    mangoldt s (f ^ m) = s f := by sorry
