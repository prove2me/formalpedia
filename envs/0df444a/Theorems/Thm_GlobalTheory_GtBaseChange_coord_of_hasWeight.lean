-- Prove2me | Theorems.Thm_GlobalTheory_GtBaseChange_coord_of_hasWeight
-- name    : GlobalTheory.GtBaseChange.coord_of_hasWeight
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T14:10:07.326975+00:00
-- url     : https://prove2.me/theorems/78bf8fe7-b948-4260-89e0-07a231222574
-- title:
--   Gt Base Change: coord of has Weight
-- statement:
--   The Gt Base Change construction uses the coord of has Weight property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoordOfHasWeight.lean#L173-L211
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/CoordOfHasWeight.lean#L173-L211

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

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
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G B : Over S} [GrpObj G] [GrpObj B]

theorem GlobalTheory.GtBaseChange.coord_of_hasWeight {K : Type} (b : Module.Basis K ℤ X) (q : G ⟶ B) (i : splitTorus S X ⟶ G)
    [hq : IsMonHom q] [hi : IsMonHom i] (hf : Flat q.left) (hs : Surjective q.left) (ha : IsAffineHom q.left)
    (hk : IsPullback i (toUnit _) q η[B]) (W : B.left.Opens) (u : K → Γ(G.left, q.left ⁻¹ᵁ W)ˣ)
    (hu : ∀ k, HasWeight i _ (u k) (b k)) (V : B.left.Opens) (hV : IsAffineOpen V) (h : V ≤ W) :
    Function.Bijective
      (AddMonoidAlgebra.liftNCRingHom (q.left.app V).hom
        ((Units.coeHom _).comp (AddMonoidHom.toMultiplicativeLeft
          (b.constr ℤ (fun k => Additive.ofMul
            (res (Scheme.Hom.preimage_mono q.left h) (u k)))).toAddMonoidHom))
        (fun _ _ => Commute.all _ _)) := by sorry
