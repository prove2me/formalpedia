-- Prove2me | Theorems.Thm_GlobalTheory_MainTerm_chainStartIndex_lt_chainLength_of_odd
-- name    : GlobalTheory.MainTerm.chainStartIndex_lt_chainLength_of_odd
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:14:14.751407+00:00
-- url     : https://prove2.me/theorems/dd3023f0-e1b9-4508-9031-3060a8613971
-- title:
--   Main Term: chain Start Index lt chain Length of odd
-- statement:
--   The Main Term construction uses the chain Start Index lt chain Length of odd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TwoMulChainStartIndexAddOneOfOdd.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TwoMulChainStartIndexAddOneOfOdd.lean#L45-L48

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
variable {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
open Classical
variable {C : Type} [Field C]
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]

theorem GlobalTheory.MainTerm.chainStartIndex_lt_chainLength_of_odd {i : ℕ} (hi : Odd i) : _root_.Formalism.BaseCaseIdentities.s0 i < _root_.Formalism.BaseCaseIdentities.Kn i := by sorry
