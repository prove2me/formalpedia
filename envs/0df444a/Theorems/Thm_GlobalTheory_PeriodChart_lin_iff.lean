-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_lin_iff
-- name    : GlobalTheory.PeriodChart.lin_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:40:40.153797+00:00
-- url     : https://prove2.me/theorems/d4e35f27-4468-4579-a25a-88be4efd12a7
-- title:
--   Period Chart: lin iff
-- statement:
--   The Period Chart construction uses the lin iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L667-L676
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L667-L676

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

theorem GlobalTheory.PeriodChart.lin_iff (P : D.La →+ (Fin g → ℂ)) :
    (∀ (a : 𝓞 E) x i, P (a • x) i = ty i (a : E) * P x i) ↔ ∀ (a : 𝓞 E) x, P (a • x) = dg ty a *ᵥ P x := by sorry
