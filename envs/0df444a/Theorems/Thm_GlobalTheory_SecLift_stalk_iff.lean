-- Prove2me | Theorems.Thm_GlobalTheory_SecLift_stalk_iff
-- name    : GlobalTheory.SecLift.stalk_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:51:22.046389+00:00
-- url     : https://prove2.me/theorems/03c5e1fb-f623-450f-ae02-a110b2d38266
-- title:
--   Sec Lift: stalk iff
-- statement:
--   The Sec Lift construction uses the stalk iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecLift.lean#L83-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/ExistsSecLift.lean#L83-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsSecLift
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.AbLaw (FirstCohomologyVanishes rs)
open GlobalTheory.SmallExtLift
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SecLift
variable {X Y Z : Scheme.{0}} {A : Type} [CommRing A]

theorem GlobalTheory.SecLift.stalk_iff {A₀ : Type} [CommRing A₀] {g : A →+* A₀} (hg : Function.Surjective g) {a : A}
    (ha : ∀ x, a * x = 0 ↔ x ∈ RingHom.ker g) {f : X ⟶ Spec (CommRingCat.of A)} [Flat f]
    {j : Y ⟶ X} {f₀ : Y ⟶ Spec (CommRingCat.of A₀)}
    (P : IsPullback j f₀ f (Spec.map (CommRingCat.ofHom g))) (y : Y)
    (e : X.presheaf.stalk (j y)) :
    cstS (𝟙 X ≫ f) (j y) a * e = 0 ↔ (j.stalkMap y).hom e = 0 := by sorry
