-- Prove2me | Theorems.Thm_GlobalTheory_GlobalModelGuards_not_isUnit
-- name    : GlobalTheory.GlobalModelGuards.not_isUnit
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T13:55:55.705695+00:00
-- url     : https://prove2.me/theorems/60b2b4cb-110f-4bc6-9cc7-abd3026116ff
-- title:
--   Global Model Guards: not is Unit
-- statement:
--   The Global Model Guards construction uses the not is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/ExistsGoodLevel.lean#L43-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/ExistsGoodLevel.lean#L43-L56

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

theorem GlobalTheory.GlobalModelGuards.not_isUnit {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ) (p : ℕ) (hW : (p : ℂ) ∈ W.nonunits) :
    ¬ IsUnit (p : c.V W) := by sorry
