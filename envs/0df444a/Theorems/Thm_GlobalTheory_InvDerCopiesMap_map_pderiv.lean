-- Prove2me | Theorems.Thm_GlobalTheory_InvDerCopiesMap_map_pderiv
-- name    : GlobalTheory.InvDerCopiesMap.map_pderiv
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:20:23.189512+00:00
-- url     : https://prove2.me/theorems/6b1d5b1b-35c3-40af-938d-6358cfa440da
-- title:
--   Inv Der Copies Map: map pderiv
-- statement:
--   The Inv Der Copies Map construction uses the map pderiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MapDofNIterate.lean#L17-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MapDofNIterate.lean#L17-L20

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_PlaceBelow
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_MapDofNIterate
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
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField
open GlobalTheory GlobalTheory.InvDerCopiesMap
open MvPowerSeries
variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

theorem GlobalTheory.InvDerCopiesMap.map_pderiv {σ : Type} (i : σ) (f : MvPowerSeries σ R) :
    MvPowerSeries.map φ (pderiv R i f) = pderiv S i (MvPowerSeries.map φ f) := by sorry
