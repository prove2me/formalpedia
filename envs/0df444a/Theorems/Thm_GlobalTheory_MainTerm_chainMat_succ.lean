-- Prove2me | Theorems.Thm_GlobalTheory_MainTerm_chainMat_succ
-- name    : GlobalTheory.MainTerm.chainMat_succ
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:25:43.881882+00:00
-- url     : https://prove2.me/theorems/f47414b4-0c8e-4619-adcc-ee8ec6cb1dfc
-- title:
--   Main Term: chain Mat succ
-- statement:
--   The Main Term construction uses the chain Mat succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TwoMulChainStartIndexAddOneOfOdd.lean#L27-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/TwoMulChainStartIndexAddOneOfOdd.lean#L27-L29

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

theorem GlobalTheory.MainTerm.chainMat_succ {Z I : Type} [Fintype I] (D : Data C Z I) (s : ℕ) (e c0 : I) :
    chainMat D (s + 1) e c0 = ∑ c ∈ Finset.univ.filter (fun c => D.lev c = s ∧ s < Kn D.i),
      (D.l : C) * D.al c 2 e * chainMat D s c c0 ^ (D.l ^ 2) := by sorry
