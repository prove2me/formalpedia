-- Prove2me | Theorems.Thm_GlobalTheory_GraphClosureExample_isFinite_str
-- name    : GlobalTheory.GraphClosureExample.isFinite_str
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T13:58:01.903804+00:00
-- url     : https://prove2.me/theorems/4c4f8b31-8445-419a-b056-b95a47656434
-- title:
--   Graph Closure Example: is Finite str
-- statement:
--   The Graph Closure Example construction uses the is Finite str property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L665-L673
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ShimuraVarieties/FlatImageOfOverFractionFieldOfValuationRing.lean#L665-L673

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

theorem GlobalTheory.GraphClosureExample.isFinite_str (d : ℤ) : IsFinite (str d) := by sorry
