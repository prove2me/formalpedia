-- Prove2me | Theorems.Thm_GlobalTheory_AbLaw_CubeGen_triv_of_local
-- name    : GlobalTheory.AbLaw.CubeGen.triv_of_local
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T10:50:34.098122+00:00
-- url     : https://prove2.me/theorems/0b7563a0-4a10-441f-a63f-117d276e3043
-- title:
--   Cube Gen: triv of local
-- statement:
--   The Cube Gen construction uses the triv of local property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivPullCompIff.lean#L74-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/TrivPullCompIff.lean#L74-L143

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

theorem GlobalTheory.AbLaw.CubeGen.triv_of_local {L : LB X} (hL : L.IsLB) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Y ⟶ T) (e : T ⟶ Y)
    (he : e ≫ p = 𝟙 T)
    (hF : ∀ (Z : Scheme.{0}) (b : Z ⟶ T) (U : Type) [CommGroup U] (k : (Z ⟶ X) → U),
      ∏ i, k ((b ≫ e) ≫ φ i) ^ ε i = 1)
    (hs : ∀ V : T.Opens, ∃ (Z : Scheme.{0}) (m : Z ⟶ Y) (q : Z ⟶ V.toScheme), IsPullback m q p V.ι ∧
      Function.Surjective q.appTop.hom)
    (h : ∀ s : T, ∃ U : T.Opens, s ∈ U ∧ TrivAt L φ ε (p ⁻¹ᵁ U).ι) : Triv (LB.LinComb L φ ε) := by sorry
