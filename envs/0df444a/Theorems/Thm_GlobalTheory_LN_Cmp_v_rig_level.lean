-- Prove2me | Theorems.Thm_GlobalTheory_LN_Cmp_v_rig_level
-- name    : GlobalTheory.LN.Cmp.v_rig_level
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T15:49:21.147909+00:00
-- url     : https://prove2.me/theorems/bf281b0c-b2fb-5ede-9d09-88e1111542c0
-- title:
--   Cmp: v rig level
-- statement:
--   The Cmp construction uses the v rig level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/ExistsUniquePartner.lean#L180-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/ExistsUniquePartner.lean#L180-L224

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

theorem GlobalTheory.LN.Cmp.v_rig_level (C : Cmp φ U U' F) (e : ℕ) {Z : Scheme.{0}} (r : Z ⟶ Spec (CommRingCat.of (V ⧸ I' ^ (e + 1))))
    (z : Z) {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig ((r ≫ thick V I' e) ≫ spMap φ) z J =
      gw C.v ((r ≫ thick V I' e) ≫ eSec D'.P.A) z (J (((r ≫ thick V I' e) ≫ spMap φ) ≫ eSec D.P.A))
          (J' ((r ≫ thick V I' e) ≫ eSec D'.P.A)) *
        val (L := D'.P.L) (φ := fun _ : PUnit => eSec D'.P.A) (ε := fun _ => 1) D'.rig (r ≫ thick V I' e) z J' := by sorry
