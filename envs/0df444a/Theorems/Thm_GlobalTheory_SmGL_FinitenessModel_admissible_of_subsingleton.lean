-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_FinitenessModel_admissible_of_subsingleton
-- name    : GlobalTheory.SmGL.FinitenessModel.admissible_of_subsingleton
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:23:50.361712+00:00
-- url     : https://prove2.me/theorems/b397feb4-c120-580f-b150-60204f00dcc2
-- title:
--   Finiteness Model: admissible of subsingleton
-- statement:
--   The Finiteness Model construction uses the admissible of subsingleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HasFiniteLengthOfFiniteDimensional.lean#L16-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HasFiniteLengthOfFiniteDimensional.lean#L16-L34

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

theorem GlobalTheory.SmGL.FinitenessModel.admissible_of_subsingleton {G V : Type} [Group G] [TopologicalSpace G] [Subsingleton G]
    [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G V) (hs : IsSmooth π)
    (h : π.IsIrreducible) : IsAdmissible π := by sorry
