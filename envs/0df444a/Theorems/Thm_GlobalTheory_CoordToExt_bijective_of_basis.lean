-- Prove2me | Theorems.Thm_GlobalTheory_CoordToExt_bijective_of_basis
-- name    : GlobalTheory.CoordToExt.bijective_of_basis
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T14:38:56.32092+00:00
-- url     : https://prove2.me/theorems/17844099-08b6-48cc-8da7-00738b5fafd2
-- title:
--   Coord To Ext: bijective of basis
-- statement:
--   The Coord To Ext construction uses the bijective of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAbelianSchemeThick.lean#L87-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAbelianSchemeThick.lean#L87-L119

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineOpenAndBijectiveOfWeightUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAbelianSchemeThick
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.CoordToExt
variable {S : Scheme.{0}}

theorem GlobalTheory.CoordToExt.bijective_of_basis {X : Type} [AddCommGroup X] {κ : Type} (b : Module.Basis κ ℤ X) {G B : Over S}
    [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : splitTorus S X ⟶ G) (hq : IsMonHom q) (hi : IsMonHom i)
    (hf : Flat q.left) (hs : Surjective q.left) (ha : IsAffineHom q.left)
    (hk : IsPullback i (toUnit _) q (η[B])) (V : B.left.Opens) (hV : IsAffineOpen V)
    (u : κ → Γ(G.left, q.left ⁻¹ᵁ V)ˣ)
    (hu : ∀ (k : κ) (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left), q.left (g.left z) ∈ V →
      gm ((t ≫ i) * g).left z _ (u k) = gm t.left z ⊤ (charUnit S X (b k)) * gm g.left z _ (u k)) :
    Function.Bijective (AddMonoidAlgebra.liftNCRingHom (q.left.app V).hom
      ((Units.coeHom _).comp (AddMonoidHom.toMultiplicativeLeft
        (b.constr ℤ (fun k => Additive.ofMul (u k))).toAddMonoidHom)) (fun _ _ => Commute.all _ _)) := by sorry
