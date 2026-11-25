-- Prove2me | Theorems.Thm_GlobalTheory_CubeLift_exists_dif
-- name    : GlobalTheory.CubeLift.exists_dif
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T14:58:15.625188+00:00
-- url     : https://prove2.me/theorems/8af5909d-1210-4b58-97a7-4fcb3aa125d5
-- title:
--   Cube Lift: exists dif
-- statement:
--   The Cube Lift construction uses the exists dif property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EvSurjective.lean#L192-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/EvSurjective.lean#L192-L219

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueTorusCompat
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_IsNilpotentOfRd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_EvSurjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
open GlobalTheory GlobalTheory.CubeLift
open SplitTorus (ev univPt ptOf pull bcMap ofVal valHom)
open ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht (chi torusFst)
variable {A : Type} [CommRing A] {X Y : Type} [AddCommGroup X] [AddCommGroup Y]
variable {J : Ideal A}

theorem GlobalTheory.CubeLift.exists_dif (hJ : IsNilpotent J) (D : Γ((splitTorus (Spec (CommRingCat.of A)) (X × X × X)).left, ⊤)ˣ)
    (s₁ : ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u : Z ⟶ splitTorus _ X),
      app (pt x y u).left D = app (pt y x u).left D)
    (s₂ : ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u : Z ⟶ splitTorus _ X),
      app (pt x y u).left D = app (pt x u y).left D)
    (co : ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u v : Z ⟶ splitTorus _ X),
      app (pt (x * y) u v).left D * app (pt x y v).left D = app (pt x (y * u) v).left D * app (pt y u v).left D)
    (h : app (bcMap (red J) _) D = 1) :
    ∃ g : Γ((splitTorus (Spec (CommRingCat.of A)) X).left, ⊤)ˣ, app (bcMap (red J) X) g = 1 ∧
      ∀ (Z : Over (Spec (CommRingCat.of A))) (x y u : Z ⟶ splitTorus _ X), app (pt x y u).left D = dif g x y u := by sorry
