-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_exists_lin_anti
-- name    : GlobalTheory.PeriodChart.exists_lin_anti
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:42:26.720073+00:00
-- url     : https://prove2.me/theorems/ee8d481f-a136-4d3e-94ae-bc39dae676cb
-- title:
--   Period Chart: exists lin anti
-- statement:
--   The Period Chart construction uses the exists lin anti property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L78-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L78-L114

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
variable {V : Type} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.PeriodChart.exists_lin_anti (T : V →+ V) (hT : ∀ (r : ℝ) z, T ((r : ℂ) • z) = (r : ℂ) • T z) :
    ∃ (A : V →ₗ[ℂ] V) (C : V →ₗ⋆[ℂ] V), ∀ z, T z = A z + C z := by sorry
