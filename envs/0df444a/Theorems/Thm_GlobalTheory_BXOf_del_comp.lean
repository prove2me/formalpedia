-- Prove2me | Theorems.Thm_GlobalTheory_BXOf_del_comp
-- name    : GlobalTheory.BXOf.del_comp
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T16:52:59.27+00:00
-- url     : https://prove2.me/theorems/69713e5c-c8ea-43e9-bed5-74842b5994bc
-- title:
--   BXOf: del comp
-- statement:
--   The BXOf construction uses the del comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BiextensionSecondLawCommutativityValue.lean#L68-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BiextensionSecondLawCommutativityValue.lean#L68-L84

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_TowerZeroSurjective
import Definitions.Def_ReciprocityTheory_DualLattices_LinPairStatement
import Definitions.Def_ReciprocityTheory_DualLattices_SubMemOfCompat
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_UniversalCharts_LePreimageOfNil
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_Biextensions_GenericFiberCubeInclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_AlWellDefSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BiextensionSecondLawCommutativityValue
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsGrpPullback_comp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct IsLocalRing Matrix CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2 ReciprocityTheory.ChartRestriction.G.Chart
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.BXOf
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
variable {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S] {X Y : Scheme.{0}}

theorem GlobalTheory.BXOf.del_comp {Q : Type} [CommRing Q] [IsLocalRing Q] {L : LB X} (hL : L.IsLB) (f : Q →+* R) (h : R →+* S)
    {JQ : (Spec (CommRingCat.of Q) ⟶ X) → L.ι} (hQ : Good L (closedPoint Q) JQ)
    {JR : (Spec (CommRingCat.of R) ⟶ X) → L.ι} (hR : Good L (closedPoint R) JR)
    {JS : (Spec (CommRingCat.of S) ⟶ X) → L.ι} (hS : Good L (closedPoint S) JS)
    (ψ : Spec (CommRingCat.of Q) ⟶ X) :
    del L (h.comp f) JQ JS ψ =
      Units.map h.toMonoidHom (del L f JQ JR ψ) * del L h JR JS (Spec.map (CommRingCat.ofHom f) ≫ ψ) := by sorry
