-- Prove2me | Theorems.Thm_GlobalTheory_SaturatedSections_cst_eq
-- name    : GlobalTheory.SaturatedSections.cst_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:12:53.645541+00:00
-- url     : https://prove2.me/theorems/a0db852c-db2e-48ee-befb-85757c2bd7ad
-- title:
--   Saturated Sections: cst eq
-- statement:
--   The Saturated Sections construction uses the cst eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueCombOfIndependentSpecialFibre.lean#L69-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueCombOfIndependentSpecialFibre.lean#L69-L70

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

theorem GlobalTheory.SaturatedSections.cst_eq {W : Type} [CommRing W] {H : Scheme.{0}} (p : H ⟶ Sp W) (U : H.Opens) (a : W) :
    Out.resTop U (Out.scal p a) = cst p U a := by sorry
