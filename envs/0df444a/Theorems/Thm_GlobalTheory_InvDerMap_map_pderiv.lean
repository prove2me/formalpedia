-- Prove2me | Theorems.Thm_GlobalTheory_InvDerMap_map_pderiv
-- name    : GlobalTheory.InvDerMap.map_pderiv
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:20:01.939026+00:00
-- url     : https://prove2.me/theorems/0db6ff49-b56e-4c06-afe2-20c272d9d699
-- title:
--   Inv Der Map: map pderiv
-- statement:
--   The Inv Der Map construction uses the map pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MapDofIterate.lean#L14-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MapDofIterate.lean#L14-L17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_MapDofIterate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open GlobalTheory GlobalTheory.InvDerMap
variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

theorem GlobalTheory.InvDerMap.map_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ R) :
    MvPowerSeries.map φ (pderiv R i f) = pderiv S i (MvPowerSeries.map φ f) := by sorry
