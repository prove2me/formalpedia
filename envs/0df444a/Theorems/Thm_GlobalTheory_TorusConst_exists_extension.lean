-- Prove2me | Theorems.Thm_GlobalTheory_TorusConst_exists_extension
-- name    : GlobalTheory.TorusConst.exists_extension
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:31:16.05214+00:00
-- url     : https://prove2.me/theorems/27fd3617-63fa-4b6b-8c4b-f0bf40535ff6
-- title:
--   Torus Const: exists extension
-- statement:
--   The Torus Const construction uses the exists extension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L68-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L68-L126

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
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
open GlobalTheory.TorusConst
open Polynomial TorusToProper
set_option backward.isDefEq.respectTransparency false

theorem GlobalTheory.TorusConst.exists_extension {W Z Y S : Scheme.{0}} [IsIntegral Z]
    (hZ : ∀ x : Z, ValuationRing (Z.presheaf.stalk x)) (w : W ⟶ Z) [IsOpenImmersion w] [Nonempty W]
    (sZ : Z ⟶ S) (sY : Y ⟶ S) [IsProper sY] [Y.IsSeparated] [S.IsSeparated] (u : W ⟶ Y)
    (hu : u ≫ sY = w ≫ sZ) : ∃ g : Z ⟶ Y, w ≫ g = u ∧ g ≫ sY = sZ := by sorry
