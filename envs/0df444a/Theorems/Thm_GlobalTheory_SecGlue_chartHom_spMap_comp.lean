-- Prove2me | Theorems.Thm_GlobalTheory_SecGlue_chartHom_spMap_comp
-- name    : GlobalTheory.SecGlue.chartHom_spMap_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:17:53.211806+00:00
-- url     : https://prove2.me/theorems/6768ed43-1a2e-4181-93e1-bf4804eb8445
-- title:
--   Sec Glue: chart Hom sp Map comp
-- statement:
--   The Sec Glue construction uses the chart Hom sp Map comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationInChartSpecMapComp.lean#L14-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsAffineCombinationInChartSpecMapComp.lean#L14-L27

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

theorem GlobalTheory.SecGlue.chartHom_spMap_comp {Y : Scheme.{0}} (V : Y.Opens) {S S' : Type} [CommRing S] [CommRing S']
    (g : S →+* S') (u : Sp S ⟶ Y) (h : u ⁻¹ᵁ V = ⊤) (h' : (spMap g ≫ u) ⁻¹ᵁ V = ⊤) (x : Γ(Y, V)) :
    chartHom V (spMap g ≫ u) h' x = g (chartHom V u h x) := by sorry
