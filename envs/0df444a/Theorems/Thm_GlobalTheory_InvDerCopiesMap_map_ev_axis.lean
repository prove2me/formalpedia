-- Prove2me | Theorems.Thm_GlobalTheory_InvDerCopiesMap_map_ev_axis
-- name    : GlobalTheory.InvDerCopiesMap.map_ev_axis
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:21:28.710799+00:00
-- url     : https://prove2.me/theorems/ed63ec7d-4653-4dee-9b48-38360636af48
-- title:
--   Inv Der Copies Map: map ev axis
-- statement:
--   The Inv Der Copies Map construction uses the map ev axis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MapDofNIterate.lean#L22-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MapDofNIterate.lean#L22-L33

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

theorem GlobalTheory.InvDerCopiesMap.map_ev_axis {d n : ℕ} (b : Fin n) (g : PS R 2 d) :
    MvPowerSeries.map φ (ev (n := n) ![pt R d b, 0] g) =
      ev (n := n) ![pt S d b, 0] (MvPowerSeries.map φ g) := by sorry
