-- Prove2me | Theorems.Thm_GlobalTheory_SmallExtLift_app_eq_zero_of_mul
-- name    : GlobalTheory.SmallExtLift.app_eq_zero_of_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:42.436994+00:00
-- url     : https://prove2.me/theorems/dcd6292e-6a1b-46bd-a8e2-ce36055075fe
-- title:
--   Small Ext Lift: app eq zero of mul
-- statement:
--   The Small Ext Lift construction uses the app eq zero of mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L421-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L421-L428

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_TangentLinearity_ConstPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsGenOfSmallExtension
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open TopologicalSpace
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false
noncomputable section
open GlobalTheory GlobalTheory.SmallExtLift
variable {X Y Z : Scheme.{0}}
variable {R : Type} [CommRing R]
variable [IsLocalRing R] {ε : R} {p : X ⟶ Spec (CommRingCat.of R)} {i : Y ⟶ X}
  {f : Y ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField R))}

theorem GlobalTheory.SmallExtLift.app_eq_zero_of_mul (hε : ε ≠ 0) [Flat p]
    (w : i ≫ p = f ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
    {V : X.Opens} (hV : IsAffineOpen V) (a : Γ(X, V)) (ha : cst p V ε * a = 0) :
    (i.app V).hom a = 0 := by sorry
