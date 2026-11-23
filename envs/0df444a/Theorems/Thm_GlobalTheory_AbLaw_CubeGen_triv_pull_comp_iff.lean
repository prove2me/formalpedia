-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_CubeGen_triv_pull_comp_iff
-- name    : GlobalTheory.AbLaw.CubeGen.triv_pull_comp_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:41:20.129002+00:00
-- url     : https://prove2.me/theorems/fe5b5811-8621-4c58-bb80-9e4329fae52f
-- title:
--   Cube Gen: triv pull comp iff
-- statement:
--   The Cube Gen construction uses the triv pull comp iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivPullCompIff.lean#L151-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivPullCompIff.lean#L151-L155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivPullCompIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen
variable {X Y T W : Scheme.{0}} {K : Type} [Fintype K] (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ)

theorem GlobalTheory.AbLaw.CubeGen.triv_pull_comp_iff (q : W ⟶ Y) {Z : Scheme.{0}} (π : Z ⟶ W) :
    Triv ((LB.LinComb L (fun k => q ≫ φ k) ε).pull π) ↔ TrivAt L φ ε (π ≫ q) := by sorry
