-- Prove2me | Theorems.Thm_GlobalTheory_InvDerMap_map_Dof
-- name    : GlobalTheory.InvDerMap.map_Dof
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:20:07.209526+00:00
-- url     : https://prove2.me/theorems/d3aa5655-aef9-4ba2-bff2-0b4d8f2cbd1b
-- title:
--   Inv Der Map: map Dof
-- statement:
--   The Inv Der Map construction uses the map Dof property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MapDofIterate.lean#L32-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MapDofIterate.lean#L32-L35

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

theorem GlobalTheory.InvDerMap.map_Dof {d : ℕ} (F : Fin d → PS R 2 d) (u : Fin d → R) (f : PS R 1 d) :
    MvPowerSeries.map φ (Dof F u f) =
      Dof (fun i => MvPowerSeries.map φ (F i)) (fun i => φ (u i)) (MvPowerSeries.map φ f) := by sorry
