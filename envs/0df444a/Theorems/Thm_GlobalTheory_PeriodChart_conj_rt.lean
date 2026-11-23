-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_conj_rt
-- name    : GlobalTheory.PeriodChart.conj_rt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:37.679796+00:00
-- url     : https://prove2.me/theorems/a2270bd0-e7dc-46d1-867c-ce7bad02322d
-- title:
--   Period Chart: conj rt
-- statement:
--   The Period Chart construction uses the conj rt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L857-L895
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L857-L895

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
variable {D : Datum H} {ty : Fin g → (E →+* ℂ)}

theorem GlobalTheory.PeriodChart.conj_rt (H : Host E) (τ : E →+* ℂ) :
    (τ (H.rt : E) = H.rt0 ↔ ¬ ComplexEmbedding.conjugate τ (H.rt : E) = H.rt0) := by sorry
