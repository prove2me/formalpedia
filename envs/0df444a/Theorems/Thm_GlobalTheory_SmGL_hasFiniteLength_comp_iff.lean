-- Prove2me | Theorems.Thm_GlobalTheory_SmGL_hasFiniteLength_comp_iff
-- name    : GlobalTheory.SmGL.hasFiniteLength_comp_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:42:29.733711+00:00
-- url     : https://prove2.me/theorems/6a53e7be-709e-4630-becd-ea8c2e2fd241
-- title:
--   Sm GL: has Finite Length comp iff
-- statement:
--   The Sm GL construction uses the has Finite Length comp iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HasFiniteLengthOfIsIrreducible.lean#L73-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/HasFiniteLengthOfIsIrreducible.lean#L73-L86

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MatrixMeasurableSpace
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_LeviEmbMemNormalizerLower
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsSubquotientDetRepParInd
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_T2SpaceGeneralLinearGroup
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_HasFiniteLengthOfIsIrreducible
import Theorems.Thm_GlobalTheory_SmGL_IsSmoothChar_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open GlobalTheory
open GlobalTheory.SmGL
variable {F G H V : Type} [Field F] [Group G] [Group H] [AddCommGroup V] [Module F V]

theorem GlobalTheory.SmGL.hasFiniteLength_comp_iff (ρ : Representation F G V) (s : H →* G) (hs : Function.Surjective s) :
    HasFiniteLength (ρ.comp s : Representation F H V) ↔ HasFiniteLength ρ := by sorry
