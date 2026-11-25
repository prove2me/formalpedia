-- Prove2me | Theorems.Thm_GlobalTheory_GraphClosureExample_isProper_and_not_isIso
-- name    : GlobalTheory.GraphClosureExample.isProper_and_not_isIso
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:05:58.683335+00:00
-- url     : https://prove2.me/theorems/eb14be8f-465c-5890-9ebf-7937842adf2f
-- title:
--   Graph Closure Example: is Proper and not is Iso
-- statement:
--   The Graph Closure Example construction uses the is Proper and not is Iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L675-L694
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L675-L694

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
universe u
open GlobalTheory
noncomputable section
open GlobalTheory.GraphClosureExample

theorem GlobalTheory.GraphClosureExample.isProper_and_not_isIso :
    IsProper (graphClosure.fst (str (-4)) (str (-1)) openPart partialMap comm) ∧
      IsIso (graphClosure.fst (str (-4)) (str (-1)) openPart partialMap comm ∣_
        openPart.opensRange) ∧
      ¬ IsIso (graphClosure.fst (str (-4)) (str (-1)) openPart partialMap comm) := by sorry
