-- Prove2me | Theorems.Thm_GlobalTheory_TorusCube_toHom_comp_val
-- name    : GlobalTheory.TorusCube.toHom_comp_val
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T03:33:26.667251+00:00
-- url     : https://prove2.me/theorems/9ee85be0-41b1-4dcf-9bb2-265ec7ceb6ba
-- title:
--   Torus Cube: to Hom comp val
-- statement:
--   The Torus Cube construction uses the to Hom comp val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SplitTorusGenCubical.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SplitTorusGenCubical.lean#L20-L24

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_OpensRangeChartYSupOpensRangeChartZ
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SplitTorusGenCubical
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorusCube
open Rosenlicht SplitTorusPoints Geo.Tor

theorem GlobalTheory.TorusCube.toHom_comp_val {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z W : Over S} (ρ : W ⟶ Z)
    (t : Z ⟶ splitTorus S X) (a : Multiplicative X) :
    (toHom (ρ ≫ t) a).val = ρ.left.appTop.hom (toHom t a).val := by sorry
