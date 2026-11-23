-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_mangoldtConv_eq_of_dvd_pow
-- name    : GlobalTheory.CuspGL.mangoldtConv_eq_of_dvd_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:32:38.856094+00:00
-- url     : https://prove2.me/theorems/271dae2f-62cd-4f00-a4d6-5270b56d7bd1
-- title:
--   Cusp GL: mangoldt Conv eq of dvd pow
-- statement:
--   The Cusp GL construction uses the mangoldt Conv eq of dvd pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AdditiveEqPolynomialVonMangoldtConvolutionOne.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AdditiveEqPolynomialVonMangoldtConvolutionOne.lean#L10-L12

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

theorem GlobalTheory.CuspGL.mangoldtConv_eq_of_dvd_pow {f g : F[X]} (hf : f.Monic) (hf' : Irreducible f) (hg : g.Monic)
    (hg' : Irreducible g) {n : ℕ} (h : g ∣ f ^ n) : g = f := by sorry
