-- Prove2me | Theorems.Thm_GlobalTheory_TauValues_even_iff
-- name    : GlobalTheory.TauValues.even_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T15:33:03.277966+00:00
-- url     : https://prove2.me/theorems/3438e19f-28e2-4700-97b5-ee1c8a7a68c5
-- title:
--   Tau Values: even iff
-- statement:
--   The Tau Values construction uses the even iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TauBimultPsiEvenOverExtensionField.lean#L78-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/TauBimultPsiEvenOverExtensionField.lean#L78-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CorrOfValFieldExtension
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultPsiEvenOverExtensionField
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
open GlobalTheory GlobalTheory.TauValues
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

theorem GlobalTheory.TauValues.even_iff {T : Over (Spec (CommRingCat.of R))} (κ : T ⟶ TK R) [Flat κ.left] [Surjective κ.left] :
    (∀ (z : T.left) J, Good D.P.L z J → ∀ m : D.X,
      val (D.psi (-m)) κ.left z J * val D.sym (cT D T m).left z J = val (D.psi m) κ.left z J) ↔ D.PsiEven := by sorry
