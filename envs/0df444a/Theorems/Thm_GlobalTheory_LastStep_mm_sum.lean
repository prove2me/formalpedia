-- Prove2me | Theorems.Thm_GlobalTheory_LastStep_mm_sum
-- name    : GlobalTheory.LastStep.mm_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:36:57.745806+00:00
-- url     : https://prove2.me/theorems/ecb9f03c-a94f-4081-9ab7-d2e3cf6c9ad9
-- title:
--   Last Step: mm sum
-- statement:
--   The Last Step construction uses the mm sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IndependentModFirstCoeffChainLastStep.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/IndependentModFirstCoeffChainLastStep.lean#L19-L25

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CharacteristicFromRanks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_TwoMulChainStartIndexAddOneOfOdd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_PowAdditiveAndRoots
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_IndependentModFirstCoeffChainLastStep
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical GlobalTheory.FrobRoot
open GlobalTheory GlobalTheory.LastStep

theorem GlobalTheory.LastStep.mm_sum {C : Type} [Field C] {V : VF C} {ι : Type} (s : Finset ι) (f : ι → C)
    (h : ∀ i ∈ s, V.MM (f i)) : V.MM (∑ i ∈ s, f i) := by sorry
