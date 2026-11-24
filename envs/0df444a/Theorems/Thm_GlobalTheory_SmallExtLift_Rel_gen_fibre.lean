-- Prove2me | Theorems.Thm_GlobalTheory_SmallExtLift_Rel_gen_fibre
-- name    : GlobalTheory.SmallExtLift.Rel.gen_fibre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:23.440065+00:00
-- url     : https://prove2.me/theorems/0c07d5cb-7741-444f-ae7e-3fd97c3cb248
-- title:
--   Rel: gen fibre
-- statement:
--   The Rel construction uses the gen fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L495-L514
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L495-L514

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

theorem GlobalTheory.SmallExtLift.Rel.gen_fibre (H : Rel p ε M V j hj u α) (hε : ε * ε = 0)
    (hm : ∀ a ∈ IsLocalRing.maximalIdeal R, a * ε = 0) [X.IsSeparated] (hM : M.IsLB)
    (hV : ⨆ a, V a = ⊤) (hA : ∀ a, IsAffineOpen (V a)) (hu : ∀ a, IsUnit (u a))
    (P : IsPullback i f p (Spec.map (CommRingCat.ofHom (IsLocalRing.residue R))))
    (ψ : ∀ a, Γ(Y, i ⁻¹ᵁ V a))
    (hψ : ∀ a b, (i.appLE (V a ⊓ V b) (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b) (fun _ h => h)).hom (α a b) =
      (Y.presheaf.map (homOfLE inf_le_left).op).hom (ψ a) -
        (Y.presheaf.map (homOfLE inf_le_right).op).hom (ψ b)) :
    ∃ t : LB.Gen M, t.IsGen := by sorry
