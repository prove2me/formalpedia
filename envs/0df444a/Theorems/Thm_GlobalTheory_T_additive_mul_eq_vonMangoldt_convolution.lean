-- Prove2me | Theorems.Thm_GlobalTheory_T_additive_mul_eq_vonMangoldt_convolution
-- name    : GlobalTheory.T.additive_mul_eq_vonMangoldt_convolution
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T20:26:11.254806+00:00
-- url     : https://prove2.me/theorems/b3c190a2-b9b9-4c61-90f7-41ed0a9b0464
-- title:
--   T: additive mul eq von Mangoldt convolution
-- statement:
--   The T construction uses the additive mul eq von Mangoldt convolution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AdditiveMulEqVonMangoldtConvolutionStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/AdditiveMulEqVonMangoldtConvolutionStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveMulEqVonMangoldtConvolution
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_AdditiveMulEqVonMangoldtConvolutionStatement
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

theorem GlobalTheory.T.additive_mul_eq_vonMangoldt_convolution : ∀ (F : Type) [Field F] (q : ℕ), 2 ≤ q → ∀ (s m : F[X] → ℂ), IsAdditive s → m 1 = 1 → (∀ P : F[X], P.Monic → (q : ℂ) ^ P.natDegree * m P = conv (fun _ => 1) m P) → ∀ P : F[X], P.Monic → s P * m P = conv (fun D => mangoldt s D / ((q : ℂ) ^ D.natDegree - 1)) m P := by sorry
