-- Prove2me | Theorems.Thm_GlobalTheory_SmallExtLift_mem_of_app_eq_zero
-- name    : GlobalTheory.SmallExtLift.mem_of_app_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:36.463178+00:00
-- url     : https://prove2.me/theorems/fed29604-4858-42cf-a1aa-b11be08ffd60
-- title:
--   Small Ext Lift: mem of app eq zero
-- statement:
--   The Small Ext Lift construction uses the mem of app eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L83-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L83-L106

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
variable {R' : Type} [CommRing R'] {φ : R →+* R'} {p : X ⟶ Spec (CommRingCat.of R)}
  {π : Y ⟶ X} {f' : Y ⟶ Spec (CommRingCat.of R')}

theorem GlobalTheory.SmallExtLift.mem_of_app_eq_zero (hφ : Function.Surjective φ)
    (H : IsPullback π f' p (Spec.map (CommRingCat.ofHom φ))) {V : X.Opens} (hV : IsAffineOpen V)
    (a : Γ(X, V)) (ha : (π.app V).hom a = 0) : a ∈ (RingHom.ker φ).map (cst p V) := by sorry
