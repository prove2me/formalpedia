-- Prove2me | Theorems.Thm_GlobalTheory_SmallExtLift_Rel_cocycle_fibre
-- name    : GlobalTheory.SmallExtLift.Rel.cocycle_fibre
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:21.106305+00:00
-- url     : https://prove2.me/theorems/eb6e8346-cf5d-466b-9cfa-9d5fe259e0e7
-- title:
--   Rel: cocycle fibre
-- statement:
--   The Rel construction uses the cocycle fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L441-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L441-L457

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
variable {M : LB X} {I : Type} {V : I → X.Opens}
  {j : I → M.ι} {hj : ∀ a, V a ≤ M.U (j a)} {u : ∀ a, Γ(X, V a)} {α : ∀ a b, Γ(X, V a ⊓ V b)}

theorem GlobalTheory.SmallExtLift.Rel.cocycle_fibre (H : Rel p ε M V j hj u α) (hε : ε * ε = 0) (h0 : ε ≠ 0) [Flat p]
    [X.IsSeparated] (hM : M.IsLB) (hA : ∀ a, IsAffineOpen (V a)) (hu : ∀ a, IsUnit (u a))
    (w : i ≫ p = f ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))) (a b d : I) (y : Y)
    (ha : (𝟙 Y ≫ i) y ∈ V a) (hb : (𝟙 Y ≫ i) y ∈ V b) (hd : (𝟙 Y ≫ i) y ∈ V d) :
    gr (𝟙 Y ≫ i) y (V a ⊓ V b) ⟨ha, hb⟩ (α a b) + gr (𝟙 Y ≫ i) y (V b ⊓ V d) ⟨hb, hd⟩ (α b d) =
      gr (𝟙 Y ≫ i) y (V a ⊓ V d) ⟨ha, hd⟩ (α a d) := by sorry
