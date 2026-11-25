-- Prove2me | Theorems.Thm_GlobalTheory_TorusLift_exists_lift
-- name    : GlobalTheory.TorusLift.exists_lift
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T16:10:25.583142+00:00
-- url     : https://prove2.me/theorems/ea026fe3-8c26-533a-a717-8fbd2e1a0f6c
-- title:
--   Torus Lift: exists lift
-- statement:
--   The Torus Lift construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PreimageEqTopOfSurjective.lean#L139-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PreimageEqTopOfSurjective.lean#L139-L163

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomEqOneOfNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsPullbackCompIsoMonHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsAffineOfIsAffinePullbackQuotientOfIsNilpotent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsPushoutQuotientMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsIsMonHomSplitTorusOfSqEqBot
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_PreimageEqTopOfSurjective
import Theorems.Thm_GlobalTheory_SqZero_UnitInChart_map

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
open GlobalTheory GlobalTheory.TorusLift

theorem GlobalTheory.TorusLift.exists_lift {A : Type} [CommRing A] (J : Ideal A) (hJ : IsNilpotent J) (X : Type)
    [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [Smooth G.hom]
    (g : (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj
        (splitTorus (Spec (CommRingCat.of A)) X) ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj G)
    {W : G.left.Opens} (hW : IsAffineOpen W) (hg : (g.left ≫ pullback.fst _ _) ⁻¹ᵁ W = ⊤) :
    ∃ f : splitTorus (Spec (CommRingCat.of A)) X ⟶ G, f.left ⁻¹ᵁ W = ⊤ ∧
      (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map f = g := by sorry
