-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_mangoldt_conv_spec
-- name    : GlobalTheory.CuspGL.mangoldt_conv_spec
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:33:18.409849+00:00
-- url     : https://prove2.me/theorems/b2c0af1c-6f85-43c9-b47c-51d06937de71
-- title:
--   Cusp GL: mangoldt conv spec
-- statement:
--   The Cusp GL construction uses the mangoldt conv spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AdditiveEqPolynomialVonMangoldtConvolutionOne.lean#L121-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AdditiveEqPolynomialVonMangoldtConvolutionOne.lean#L121-L129

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

theorem GlobalTheory.CuspGL.mangoldt_conv_spec : ∀ (F : Type) [Field F] (s : F[X] → ℂ), IsAdditive s →
    (∀ P : F[X], P.Monic → s P = conv (mangoldt s) (fun _ => 1) P) ∧
    (∀ (f : F[X]) (m : ℕ), f.Monic → Irreducible f → 0 < m → mangoldt s (f ^ m) = s f) ∧
    ∀ P : F[X], (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) →
      mangoldt s P = 0 := by sorry
