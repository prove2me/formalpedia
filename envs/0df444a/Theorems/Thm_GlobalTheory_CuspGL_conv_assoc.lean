-- Prove2me | Theorems.Thm_GlobalTheory_CuspGL_conv_assoc
-- name    : GlobalTheory.CuspGL.conv_assoc
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:31:23.948799+00:00
-- url     : https://prove2.me/theorems/a6a64956-1f9f-44e4-8acf-efa04cc43fc8
-- title:
--   Cusp GL: conv assoc
-- statement:
--   The Cusp GL construction uses the conv assoc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MonicFactorizationConvolutionFiniteCommAssocAdd.lean#L42-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CharacterTheory/MonicFactorizationConvolutionFiniteCommAssocAdd.lean#L42-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_CommutativeAlgebra_InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CharacterTheory_MonicFactorizationConvolutionFiniteCommAssocAdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial GlobalTheory.CuspGL
open GlobalTheory GlobalTheory.CuspGL
variable {F : Type} [Field F]

theorem GlobalTheory.CuspGL.conv_assoc (a b c : F[X] → ℂ) (P : F[X]) :
    conv (conv a b) c P = conv a (conv b c) P := by sorry
