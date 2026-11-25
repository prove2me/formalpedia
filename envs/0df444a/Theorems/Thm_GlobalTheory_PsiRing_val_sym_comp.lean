-- Prove2me | Theorems.Thm_GlobalTheory_PsiRing_val_sym_comp
-- name    : GlobalTheory.PsiRing.val_sym_comp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T16:12:53.379562+00:00
-- url     : https://prove2.me/theorems/4add9579-9710-4025-bf4d-80609f74692b
-- title:
--   Psi Ring: val sym comp
-- statement:
--   The Psi Ring construction uses the val sym comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PsiEvenDescendBaseChange.lean#L34-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/PsiEvenDescendBaseChange.lean#L34-L70

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValEqOfAppInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SecCmp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PsiEvenDescendBaseChange
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
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
noncomputable section
open GlobalTheory GlobalTheory.PsiRing
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V} {D : DegPre R}
  {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left} {v : LB.Iso D'.P.L (D.P.L.pull β)}

theorem GlobalTheory.PsiRing.val_sym_comp (hG : GlobalFnsSt) (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β) (hv₀ : v.IsGen)
    {Z : Scheme.{0}} (r : Z ⟶ D'.P.A.left) (z : Z) {J J'} (hJ : Good D.P.L z J) (hJ' : Good D'.P.L z J') :
    val D.sym (r ≫ β) z J =
      gw v (r ≫ (ι[D'.P.A]).left) z (J ((r ≫ (ι[D'.P.A]).left) ≫ β)) (J' (r ≫ (ι[D'.P.A]).left)) *
        (gw v r z (J (r ≫ β)) (J' r))⁻¹ * val D'.sym r z J' := by sorry
