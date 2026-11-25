-- Prove2me | Theorems.Thm_GlobalTheory_GlobalModelGuards_exists_place
-- name    : GlobalTheory.GlobalModelGuards.exists_place
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:04.474867+00:00
-- url     : https://prove2.me/theorems/ddb50979-21c8-44e5-8d40-d4657cdc3d70
-- title:
--   Global Model Guards: exists place
-- statement:
--   The Global Model Guards construction uses the exists place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/ExistsGoodLevel.lean#L13-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/ExistsGoodLevel.lean#L13-L28

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Clauses
import Definitions.Def_Development_AbelianVarietyTheory_Counterexamples_ModuliSurvey_ExistsGoodLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.GlobalModelGuards
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

theorem GlobalTheory.GlobalModelGuards.exists_place (p : ℕ) (hp : p.Prime) : ∃ W : ValuationSubring ℂ, (p : ℂ) ∈ W.nonunits := by sorry
