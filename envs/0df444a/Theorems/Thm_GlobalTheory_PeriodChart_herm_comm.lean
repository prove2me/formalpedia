-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_herm_comm
-- name    : GlobalTheory.PeriodChart.herm_comm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:42:20.822709+00:00
-- url     : https://prove2.me/theorems/5259d4a2-3ba7-4f36-90cb-0ad21b52ec7f
-- title:
--   Period Chart: herm comm
-- statement:
--   The Period Chart construction uses the herm comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L678-L718
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L678-L718

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

theorem GlobalTheory.PeriodChart.herm_comm (P : D.La →+ (Fin g → ℂ)) (hl : ∀ (a : 𝓞 E) x, P (a • x) = dg ty a *ᵥ P x)
    (hs : Submodule.span ℝ (Set.range P) = ⊤) (G : Matrix (Fin g) (Fin g) ℂ)
    (hE : ∀ x y, (sesq G (P x) (P y)).im = D.EF x y) (a : 𝓞 E) : dg ty a * Gᵀ = Gᵀ * dg ty a := by sorry
