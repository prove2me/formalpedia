-- Prove2me | Theorems.Thm_GlobalTheory_TorusLift_main
-- name    : GlobalTheory.TorusLift.main
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T16:06:07.509066+00:00
-- url     : https://prove2.me/theorems/81e8ee2d-a04a-4fd1-9c55-f2c9a70c851c
-- title:
--   Torus Lift: main
-- statement:
--   The Torus Lift construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PreimageEqTopOfSurjective.lean#L341-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/PreimageEqTopOfSurjective.lean#L341-L364

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
import Theorems.Thm_GlobalTheory_IrreducibleGeneralizations_main
import Theorems.Thm_GlobalTheory_NilpotentLift_main
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

theorem GlobalTheory.TorusLift.main : ∀ (A : Type) [CommRing A] [IsLocalRing A] (J : Ideal A), IsNilpotent J → ∀ (X : Type) [AddCommGroup X] (G : Over (Spec (CommRingCat.of A))) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (i₀ : (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj (splitTorus (Spec (CommRingCat.of A)) X) ⟶ (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj G), IsMonHom i₀ → (∃ W : ((Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).obj G).left.Opens, IsAffineOpen W ∧ i₀.left ⁻¹ᵁ W = ⊤) → ∃! i : splitTorus (Spec (CommRingCat.of A)) X ⟶ G, IsMonHom i ∧ (Over.pullback (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk J)))).map i = i₀ := by sorry
