-- Prove2me | Theorems.Thm_GlobalTheory_ChainStep_mm_of_tan
-- name    : GlobalTheory.ChainStep.mm_of_tan
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:39:21.031346+00:00
-- url     : https://prove2.me/theorems/1d8fd6d2-2037-478a-8a62-49e881179cb0
-- title:
--   Chain Step: mm of tan
-- statement:
--   The Chain Step construction uses the mm of tan property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainStepKernelRankLeModMaxIdeal.lean#L93-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainStepKernelRankLeModMaxIdeal.lean#L93-L106

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ChainStepKernelRankLeModMaxIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical
noncomputable section
open GlobalTheory GlobalTheory.ChainStep
variable {C : Type} [Field C] {V : VF C}

theorem GlobalTheory.ChainStep.mm_of_tan {d : ℕ} {I J : Type} [Fintype I] [Fintype J] {G : Cart V d I J} (S : Sys G)
    (z : I → C) (h : ∀ k, V.MM (∑ c, z c * S.tan c k)) (c : I) : V.MM (z c) := by sorry
