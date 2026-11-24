-- Prove2me | Theorems.Thm_GlobalTheory_SaturatedSections_eq_zero_of_cst_mul
-- name    : GlobalTheory.SaturatedSections.eq_zero_of_cst_mul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:42:25.12745+00:00
-- url     : https://prove2.me/theorems/af9150d3-f272-4e71-a59c-823039d3d6c4
-- title:
--   Saturated Sections: eq zero of cst mul
-- statement:
--   The Saturated Sections construction uses the eq zero of cst mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueCombOfIndependentSpecialFibre.lean#L74-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueCombOfIndependentSpecialFibre.lean#L74-L93

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
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.SaturatedSections.eq_zero_of_cst_mul {W : Type} [CommRing W] [IsDomain W] {H : Scheme.{0}} (p : H ⟶ Sp W)
    [Flat p] (V : H.Opens) {r : W} (hr : r ≠ 0) (a : Γ(H, V)) (h : cst p V r * a = 0) :
    a = 0 := by sorry
