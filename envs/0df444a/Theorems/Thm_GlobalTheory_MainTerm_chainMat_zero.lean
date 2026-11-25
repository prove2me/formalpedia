-- Prove2me | Theorems.Thm_GlobalTheory_MainTerm_chainMat_zero
-- name    : GlobalTheory.MainTerm.chainMat_zero
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:25:54.080926+00:00
-- url     : https://prove2.me/theorems/32f04c95-d555-44b9-8b1f-5c4a1530133f
-- title:
--   Main Term: chain Mat zero
-- statement:
--   The Main Term construction uses the chain Mat zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TwoMulChainStartIndexAddOneOfOdd.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TwoMulChainStartIndexAddOneOfOdd.lean#L24-L25

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds
open Formalism.BaseCaseIdentities (Data Kn s0)
open Classical
noncomputable section
open GlobalTheory GlobalTheory.MainTerm
variable {C : Type} [Field C]

theorem GlobalTheory.MainTerm.chainMat_zero {Z I : Type} [Fintype I] (D : Data C Z I) (e c0 : I) :
    chainMat D 0 e c0 = if e = c0 then 1 else 0 := by sorry
