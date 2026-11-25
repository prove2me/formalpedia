-- Prove2me | Theorems.Thm_GlobalTheory_GtBaseChange_HasWeight_baseChange
-- name    : GlobalTheory.GtBaseChange.HasWeight.baseChange
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:09:46.861899+00:00
-- url     : https://prove2.me/theorems/c6bbef3c-6225-4b70-a393-2da0dc3bd18e
-- title:
--   Has Weight: base Change
-- statement:
--   The Has Weight construction uses the base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoordOfHasWeight.lean#L219-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoordOfHasWeight.lean#L219-L240

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPullbackPullbackMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CoordOfHasWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] SplitExt.free SplitExt.finite
noncomputable section
open GlobalTheory
open GlobalTheory.GtBaseChange
variable {S S' : Scheme.{0}} (f : S' ⟶ S)

theorem GlobalTheory.GtBaseChange.HasWeight.baseChange {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] {i : splitTorus S X ⟶ G}
    {U : G.left.Opens} {u : Γ(G.left, U)ˣ} {χ : X} (hu : HasWeight i U u χ)
    (i' : splitTorus S' X ⟶ (Over.pullback f).obj G) (τ : (splitTorus S' X).left ⟶ (splitTorus S X).left)
    (hτ : τ ≫ (splitTorus S X).hom = (splitTorus S' X).hom ≫ f)
    (hi : i'.left ≫ pullback.fst G.hom f = τ ≫ i.left)
    (hc : τ.appTop.hom (charUnit S X χ).val = (charUnit S' X χ).val)
    {U' : ((Over.pullback f).obj G).left.Opens} (le : U' ≤ pullback.fst G.hom f ⁻¹ᵁ U)
    (hU' : ∀ (Z : Over S') (t : Z ⟶ splitTorus S' X) (g : Z ⟶ (Over.pullback f).obj G) (z : Z.left),
      g.left z ∈ U' → ((t ≫ i') * g).left z ∈ U') :
    HasWeight i' U' (res le (pullU (pullback.fst G.hom f) U u)) χ := by sorry
