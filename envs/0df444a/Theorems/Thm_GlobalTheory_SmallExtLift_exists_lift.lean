-- Prove2me | Theorems.Thm_GlobalTheory_SmallExtLift_exists_lift
-- name    : GlobalTheory.SmallExtLift.exists_lift
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:33.696294+00:00
-- url     : https://prove2.me/theorems/1ce29a7b-6fc1-45cd-8f4b-70f712cbbb5e
-- title:
--   Small Ext Lift: exists lift
-- statement:
--   The Small Ext Lift construction uses the exists lift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L251-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L251-L291

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

theorem GlobalTheory.SmallExtLift.exists_lift {ε : R} (hε : ε * ε = 0) {p : X ⟶ Spec (CommRingCat.of R)} [X.IsSeparated]
    {π : Y ⟶ X} {f' : Y ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))}
    (H : IsPullback π f' p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))))
    {M : LB X} (hM : M.IsLB) (t : LB.Gen (M.pull π)) (ht : t.IsGen) :
    ∃ (I : Type) (V : I → X.Opens) (j : I → M.ι) (hj : ∀ a, V a ≤ M.U (j a))
      (u : ∀ a, Γ(X, V a)) (α : ∀ a b, Γ(X, V a ⊓ V b)),
      ⨆ a, V a = ⊤ ∧ (∀ a, IsAffineOpen (V a)) ∧ (∀ a, IsUnit (u a)) ∧ Rel p ε M V j hj u α := by sorry
