-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_dg_map
-- name    : GlobalTheory.PeriodChart.dg_map
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:16:58.559586+00:00
-- url     : https://prove2.me/theorems/293fee4e-9321-5526-b53e-b01f8f4b5528
-- title:
--   Period Chart: dg map
-- statement:
--   The Period Chart construction uses the dg map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L625-L629
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L625-L629

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsContraction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PeriodChart
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}
omit [NumberField E] [IsCMField E]

theorem GlobalTheory.PeriodChart.dg_map (ty : Fin g → (E →+* ℂ)) (a : 𝓞 E) :
    (dg ty a).map (starRingEnd ℂ) = dg (fun i => ComplexEmbedding.conjugate (ty i)) a := by sorry
