-- Prove2me | Theorems.Thm_GlobalTheory_PeriodChart_isPeriod_add
-- name    : GlobalTheory.PeriodChart.isPeriod_add
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:42:24.373524+00:00
-- url     : https://prove2.me/theorems/792cbbcf-8607-49f0-bca3-d7bcde94838c
-- title:
--   Period Chart: is Period add
-- statement:
--   The Period Chart construction uses the is Period add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L720-L756
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ToricGeometry/ExistsContraction.lean#L720-L756

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

theorem GlobalTheory.PeriodChart.isPeriod_add (P : D.La →+ (Fin g → ℂ)) (hl : ∀ (a : 𝓞 E) x, P (a • x) = dg ty a *ᵥ P x)
    (hi : Function.Injective P) (hd : DiscreteTopology P.range)
    (hs : Submodule.span ℝ (Set.range P) = ⊤) (G : Matrix (Fin g) (Fin g) ℂ) (hG : G.IsHermitian)
    (hE : ∀ x y, (sesq G (P x) (P y)).im = D.EF x y) (Z : Matrix (Fin g) (Fin g) ℂ)
    (h1 : ∀ a z, anti Z (dg ty a *ᵥ z) = dg ty a *ᵥ anti Z z)
    (h2 : ∀ z w, sesq G (anti Z z) w = sesq G (anti Z w) z)
    (h3 : ∀ z, z ≠ 0 → (sesq G (anti Z z) (anti Z z)).re < (sesq G z z).re) :
    IsPeriod D ty (P + (anti Z).toAddMonoidHom.comp P) := by sorry
