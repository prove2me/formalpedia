-- Prove2me | Theorems.Thm_GlobalTheory_ChainStep_mm_mul_int
-- name    : GlobalTheory.ChainStep.mm_mul_int
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:32:40.296492+00:00
-- url     : https://prove2.me/theorems/93f529df-2d64-44f5-9646-d509fdc2c7d6
-- title:
--   Chain Step: mm mul int
-- statement:
--   The Chain Step construction uses the mm mul int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainStepKernelRankLeModMaxIdeal.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ChainStepKernelRankLeModMaxIdeal.lean#L29-L33

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

theorem GlobalTheory.ChainStep.mm_mul_int {a b : C} (ha : V.MM a) (hb : V.Ge 0 b) : V.MM (a * b) := by sorry
