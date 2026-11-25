-- Prove2me | Theorems.Thm_GlobalTheory_MainTerm_isSat_tan
-- name    : GlobalTheory.MainTerm.isSat_tan
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:13:49.772684+00:00
-- url     : https://prove2.me/theorems/518892be-0107-55c6-b693-27c1b840d732
-- title:
--   Main Term: is Sat tan
-- statement:
--   The Main Term construction uses the is Sat tan property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TwoMulChainStartIndexAddOneOfOdd.lean#L235-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TwoMulChainStartIndexAddOneOfOdd.lean#L235-L251

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
variable {G : Cart V d I J} {S : Sys G} {Z : Type} {D : Data C Z I} {a : ZMod d} {i : ℕ}
open Classical
variable {C : Type} [Field C]
variable {V : _root_.Formalism.L2.FormalSeriesBounds.VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]
variable {G : _root_.Formalism.L2.FormalSeriesBounds.Cart V d I J} {S : _root_.Formalism.L2.FormalSeriesBounds.Sys G} {Z : Type} {D : _root_.Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d}
  {i : ℕ}

theorem GlobalTheory.MainTerm.isSat_tan (S : _root_.Formalism.L2.FormalSeriesBounds.Sys G) {N : ℕ} (em : Fin N ↪ I) :
    _root_.Formalism.L2.FormalSeriesBounds.IsSat V (fun δ => S.tan (em δ)) := by sorry
