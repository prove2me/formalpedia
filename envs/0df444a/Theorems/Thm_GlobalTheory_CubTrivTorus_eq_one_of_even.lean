-- Prove2me | Theorems.Thm_GlobalTheory_CubTrivTorus_eq_one_of_even
-- name    : GlobalTheory.CubTrivTorus.eq_one_of_even
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T15:08:53.616467+00:00
-- url     : https://prove2.me/theorems/2a258048-a32e-560a-b1bd-25bb600692eb
-- title:
--   Cub Triv Torus: eq one of even
-- statement:
--   The Cub Triv Torus construction uses the eq one of even property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CubTrivDeltaAndEvenUnique.lean#L97-L175
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/CubTrivDeltaAndEvenUnique.lean#L97-L175

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueCharacterOfMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ConnectedSpaceOfSection
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ThickenedPointToTorusExtensionGenerator
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubTrivDeltaAndEvenUnique
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
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubTrivTorus
variable {S : Scheme.{0}} {X : Type} [AddCommGroup X]

theorem GlobalTheory.CubTrivTorus.eq_one_of_even [ConnectedSpace S] [Module.Free ℤ X] (u : Γ((splitTorus S X).left, ⊤)ˣ)
    (h₃ : ∀ (Z : Over S) (x y w : Z ⟶ splitTorus S X) (z : Z.left),
      gm (x * y * w).left z ⊤ u * gm x.left z ⊤ u * gm y.left z ⊤ u * gm w.left z ⊤ u =
        gm (x * y).left z ⊤ u * gm (x * w).left z ⊤ u * gm (y * w).left z ⊤ u)
    (h₁ : ∀ (Z : Over S) (z : Z.left), gm (1 : Z ⟶ splitTorus S X).left z ⊤ u = 1)
    (he : ∀ (Z : Over S) (x : Z ⟶ splitTorus S X) (z : Z.left), gm (x⁻¹).left z ⊤ u = gm x.left z ⊤ u) : u = 1 := by sorry
