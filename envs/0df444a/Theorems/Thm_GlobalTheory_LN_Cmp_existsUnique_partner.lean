-- Prove2me | Theorems.Thm_GlobalTheory_LN_Cmp_existsUnique_partner
-- name    : GlobalTheory.LN.Cmp.existsUnique_partner
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:48:25.587831+00:00
-- url     : https://prove2.me/theorems/dad83d86-e328-5a3d-945d-818b31a7fa56
-- title:
--   Cmp: exists Unique partner
-- statement:
--   The Cmp construction uses the exists Unique partner property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/ExistsUniquePartner.lean#L154-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/ExistsUniquePartner.lean#L154-L158

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.LN
open GlobalTheory.UU
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {I : Ideal R} {I' : Ideal V}
  {D : DegPre R} {D' : DegPre V} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of V))} [GrpObj G'] [IsCommMonObj G']
open GlobalTheory.LN.Cmp
variable {φ : R →+* V} {U : PreU I D A G} {U' : PreU I' D' A' G'} {F : G'.left ⟶ G.left}

theorem GlobalTheory.LN.Cmp.existsUnique_partner (C : Cmp φ U U' F) (e : ℕ) {Z : Scheme.{0}} (x' : Z ⟶ (thickObj V I' e G').left) :
    ∃! x : Z ⟶ (thickObj R I e G).left, x ≫ (fstG I e G).left = x' ≫ (fstG I' e G').left ≫ F := by sorry
