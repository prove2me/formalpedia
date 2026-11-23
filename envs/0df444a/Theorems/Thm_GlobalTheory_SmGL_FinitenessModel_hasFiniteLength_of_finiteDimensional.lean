-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_FinitenessModel_hasFiniteLength_of_finiteDimensional
-- name    : GlobalTheory.SmGL.FinitenessModel.hasFiniteLength_of_finiteDimensional
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:14:33.348098+00:00
-- url     : https://prove2.me/theorems/430a06d7-a6df-4ca4-bb46-914cb7afef38
-- title:
--   Finiteness Model: has Finite Length of finite Dimensional
-- statement:
--   The Finiteness Model construction uses the has Finite Length of finite Dimensional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HasFiniteLengthOfFiniteDimensional.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HasFiniteLengthOfFiniteDimensional.lean#L36-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SecondCountableAndT2LocalField
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfFiniteDimensional
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.PRep GlobalTheory.SmGL
open GlobalTheory GlobalTheory.SmGL GlobalTheory.SmGL.FinitenessModel

theorem GlobalTheory.SmGL.FinitenessModel.hasFiniteLength_of_finiteDimensional {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (π : Representation ℂ G V) : HasFiniteLength π := by sorry
