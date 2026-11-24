-- Prove2me | Theorems.Thm_GlobalTheory_InvDerCopiesMap_map_DofN
-- name    : GlobalTheory.InvDerCopiesMap.map_DofN
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T17:20:02.877778+00:00
-- url     : https://prove2.me/theorems/3dcd221b-d8cc-49ce-ae15-21a1352f2154
-- title:
--   Inv Der Copies Map: map Dof N
-- statement:
--   The Inv Der Copies Map construction uses the map Dof N property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MapDofNIterate.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/MapDofNIterate.lean#L35-L38

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

theorem GlobalTheory.InvDerCopiesMap.map_DofN {d n : ℕ} (F : Fin d → PS R 2 d) (b : Fin n) (u : Fin d → R) (f : PS R n d) :
    MvPowerSeries.map φ (DofN F b u f) =
      DofN (fun i => MvPowerSeries.map φ (F i)) b (fun i => φ (u i)) (MvPowerSeries.map φ f) := by sorry
