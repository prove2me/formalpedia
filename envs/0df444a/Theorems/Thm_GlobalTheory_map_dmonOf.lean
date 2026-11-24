-- Prove2me | Theorems.Thm_GlobalTheory_map_dmonOf
-- name    : GlobalTheory.map_dmonOf
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:09:50.295608+00:00
-- url     : https://prove2.me/theorems/63f26c4c-bc45-4b65-8002-9efad10c3d40
-- title:
--   Global Theory: map dmon Of
-- statement:
--   The Global Theory construction uses the map dmon Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MapDofIterate.lean#L48-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/MapDofIterate.lean#L48-L55

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
open GlobalTheory

theorem GlobalTheory.map_dmonOf (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (d : ℕ) (F : Fin d → PS R 2 d)
    (ι : Type) [Fintype ι] (u : ι → Fin d → R) (m : ι →₀ ℕ) (f : PS R 1 d) :
    MvPowerSeries.map φ (DmonOf F u m f) =
      DmonOf (fun i => MvPowerSeries.map φ (F i)) (fun l i => φ (u l i)) m (MvPowerSeries.map φ f) := by sorry
