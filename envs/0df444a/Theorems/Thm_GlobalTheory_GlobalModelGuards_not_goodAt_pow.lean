-- Prove2me | Theorems.Thm_GlobalTheory_GlobalModelGuards_not_goodAt_pow
-- name    : GlobalTheory.GlobalModelGuards.not_goodAt_pow
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:06:06.868376+00:00
-- url     : https://prove2.me/theorems/a86f0322-c63c-57fe-b162-4b9a0d032314
-- title:
--   Global Model Guards: not good At pow
-- statement:
--   The Global Model Guards construction uses the not good At pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/ExistsGoodLevel.lean#L78-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/ExistsGoodLevel.lean#L78-L82

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

theorem GlobalTheory.GlobalModelGuards.not_goodAt_pow (l : Level H) (p k : ℕ) (hp : p.Prime) (hM : l.M = p ^ k) : ¬ l.GoodAt p := by sorry
