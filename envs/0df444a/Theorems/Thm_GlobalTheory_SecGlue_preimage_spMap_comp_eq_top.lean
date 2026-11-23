-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_preimage_spMap_comp_eq_top
-- name    : GlobalTheory.SecGlue.preimage_spMap_comp_eq_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:55.553421+00:00
-- url     : https://prove2.me/theorems/7070632a-d8de-4279-a1c8-6294475760d6
-- title:
--   Sec Glue: preimage sp Map comp eq top
-- statement:
--   The Sec Glue construction uses the preimage sp Map comp eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationInChartSpecMapComp.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationInChartSpecMapComp.lean#L10-L12

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsCombIn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsAffineCombinationInChartSpecMapComp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.SecGlue

theorem GlobalTheory.SecGlue.preimage_spMap_comp_eq_top {Y : Scheme.{0}} {V : Y.Opens} {S S' : Type} [CommRing S] [CommRing S']
    (g : S →+* S') {u : Sp S ⟶ Y} (h : u ⁻¹ᵁ V = ⊤) : (spMap g ≫ u) ⁻¹ᵁ V = ⊤ := by sorry
