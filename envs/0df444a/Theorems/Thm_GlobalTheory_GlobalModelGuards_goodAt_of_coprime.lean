-- Prove2me | Theorems.Thm_GlobalTheory_GlobalModelGuards_goodAt_of_coprime
-- name    : GlobalTheory.GlobalModelGuards.goodAt_of_coprime
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T13:55:37.755169+00:00
-- url     : https://prove2.me/theorems/68f8ce90-a6a8-4f77-8c29-75cd2e1d462c
-- title:
--   Global Model Guards: good At of coprime
-- statement:
--   The Global Model Guards construction uses the good At of coprime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/ExistsGoodLevel.lean#L67-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Counterexamples/ModuliSurvey/ExistsGoodLevel.lean#L67-L76

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

theorem GlobalTheory.GlobalModelGuards.goodAt_of_coprime (l : Level H) (a b : ℕ) (ha : 3 ≤ a) (hb : 3 ≤ b) (hab : a.Coprime b)
    (hM : l.M = a * b) (p : ℕ) (hp : p.Prime) : l.GoodAt p := by sorry
