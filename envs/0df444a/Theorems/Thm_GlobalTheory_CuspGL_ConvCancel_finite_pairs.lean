-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_ConvCancel_finite_pairs
-- name    : GlobalTheory.CuspGL.ConvCancel.finite_pairs
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T12:29:37.022175+00:00
-- url     : https://prove2.me/theorems/381a3c68-5dbc-4757-9af1-36b18c8cadc6
-- title:
--   Conv Cancel: finite pairs
-- statement:
--   The Conv Cancel construction uses the finite pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MonicFactorizationConvolutionCancelOfOne.lean#L8-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MonicFactorizationConvolutionCancelOfOne.lean#L8-L16

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionCancelOfOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL GlobalTheory.CuspGL.ConvCancel

theorem GlobalTheory.CuspGL.ConvCancel.finite_pairs {F : Type} [Field F] (P : F[X]) (hP : P ≠ 0) :
    {x : F[X] × F[X] | x.1.Monic ∧ x.2.Monic ∧ x.1 * x.2 = P}.Finite := by sorry
