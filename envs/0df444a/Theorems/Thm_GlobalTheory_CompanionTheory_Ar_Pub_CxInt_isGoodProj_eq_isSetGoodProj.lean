-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxInt_isGoodProj_eq_isSetGoodProj
-- name    : GlobalTheory.CompanionTheory.Ar.Pub.CxInt.isGoodProj_eq_isSetGoodProj
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:00:39.665137+00:00
-- url     : https://prove2.me/theorems/5920f0cc-1ffb-44f3-bb63-8cca89bdd054
-- title:
--   Cx Int: is Good Proj eq is Set Good Proj
-- statement:
--   The Cx Int construction uses the is Good Proj eq is Set Good Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Metrics₂/SheetDensityEqSetSheetDensity.lean#L61-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Metrics₂/SheetDensityEqSetSheetDensity.lean#L61-L63

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_P2M_Def_Development_AutomorphicSpectrum_PublishedTheorems_Metrics__SheetDensityEqSetSheetDensity_cb85824e9bfdd8ba
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Pub
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.ChartRestriction.G.Geo
open GlobalTheory.CompanionTheory.Ar.Pub.CxInt
set_option linter.unusedSectionVars false
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {e : ℕ}

theorem GlobalTheory.CompanionTheory.Ar.Pub.CxInt.isGoodProj_eq_isSetGoodProj (P : Ideal (MRing ι))
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    IsGoodProj P Ψ = IsSetGoodProj (mcPts P) Ψ := by sorry
