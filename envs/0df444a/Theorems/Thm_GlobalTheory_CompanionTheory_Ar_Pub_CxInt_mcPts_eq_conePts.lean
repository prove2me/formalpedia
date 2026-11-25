-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Pub_CxInt_mcPts_eq_conePts
-- name    : GlobalTheory.CompanionTheory.Ar.Pub.CxInt.mcPts_eq_conePts
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:00:24.890728+00:00
-- url     : https://prove2.me/theorems/75f5ba99-b6a0-518c-adf8-a80550d6c83a
-- title:
--   Cx Int: mc Pts eq cone Pts
-- statement:
--   The Cx Int construction uses the mc Pts eq cone Pts property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Metrics₂/SheetDensityEqSetSheetDensity.lean#L67-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/PublishedTheorems/Metrics₂/SheetDensityEqSetSheetDensity.lean#L67-L75

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

theorem GlobalTheory.CompanionTheory.Ar.Pub.CxInt.mcPts_eq_conePts {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) :
    mcPts P = ReciprocityTheory.AnForm.R.conePts (P.map (map (Int.castRingHom ℂ) : MRing ι →+* MRingOver ℂ ι)) := by sorry
