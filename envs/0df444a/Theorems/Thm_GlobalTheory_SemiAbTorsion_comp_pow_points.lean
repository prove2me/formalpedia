-- Prove2me | Theorems.Thm_GlobalTheory_SemiAbTorsion_comp_pow_points
-- name    : GlobalTheory.SemiAbTorsion.comp_pow_points
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:58:11.777298+00:00
-- url     : https://prove2.me/theorems/ff1cc6b8-4871-4fa3-9bf7-2fb31c3b76dd
-- title:
--   Semi Ab Torsion: comp pow points
-- statement:
--   The Semi Ab Torsion construction uses the comp pow points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SemiAbelianTorsionFiniteAndClosedPointFiniteOrde.lean#L105-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SemiAbelianTorsionFiniteAndClosedPointFiniteOrde.lean#L105-L109

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_JacobsonClosedPointsToolsInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SemiAbelianTorsionFiniteAndClosedPointFiniteOrde
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
open GlobalTheory
open GlobalTheory.SemiAbTorsion

theorem GlobalTheory.SemiAbTorsion.comp_pow_points {S : Scheme.{0}} {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) (g : T ⟶ A)
    (n : ℕ) : f ≫ g ^ n = (f ≫ g) ^ n := by sorry
