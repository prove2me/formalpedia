-- Prove2me | Theorems.Thm_GlobalTheory_SaturatedSections_not_mem_basicOpen_cst
-- name    : GlobalTheory.SaturatedSections.not_mem_basicOpen_cst
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T19:48:36.616251+00:00
-- url     : https://prove2.me/theorems/ee850f49-c789-4b26-b70a-ebf40cb96bd8
-- title:
--   Saturated Sections: not mem basic Open cst
-- statement:
--   The Saturated Sections construction uses the not mem basic Open cst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueCombOfIndependentSpecialFibre.lean#L95-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueCombOfIndependentSpecialFibre.lean#L95-L103

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueCombOfIndependentSpecialFibre
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.SaturatedSections

theorem GlobalTheory.SaturatedSections.not_mem_basicOpen_cst {W : Type} [CommRing W] [IsLocalRing W] {H : Scheme.{0}}
    (p : H ⟶ Sp W) (V : H.Opens) {r : W} (hr : r ∈ IsLocalRing.maximalIdeal W) (x : H)
    (hx : p x = IsLocalRing.closedPoint W) : x ∉ H.basicOpen (cst p V r) := by sorry
