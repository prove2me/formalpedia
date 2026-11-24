-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_CubeGen_triv_pull_iff
-- name    : GlobalTheory.AbLaw.CubeGen.triv_pull_iff
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:51:04.20454+00:00
-- url     : https://prove2.me/theorems/c46b38c6-9c5e-466b-bea5-d1c91c61f26f
-- title:
--   Cube Gen: triv pull iff
-- statement:
--   The Cube Gen construction uses the triv pull iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivPullCompIff.lean#L28-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivPullCompIff.lean#L28-L64

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
variable {X Y Z Z' T : Scheme.{0}} {K : Type} [Fintype K]

theorem GlobalTheory.AbLaw.CubeGen.triv_pull_iff (L : LB X) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (r : Z ⟶ Y) :
    Triv ((LB.LinComb L φ ε).pull r) ↔ TrivAt L φ ε r := by sorry
