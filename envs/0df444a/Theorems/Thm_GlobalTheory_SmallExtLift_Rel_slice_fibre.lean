-- Prove2me | Theorems.Thm_GlobalTheory_SmallExtLift_Rel_slice_fibre
-- name    : GlobalTheory.SmallExtLift.Rel.slice_fibre
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:34.655811+00:00
-- url     : https://prove2.me/theorems/a45cdd45-f69c-421e-b9f9-b1c8c9006bb5
-- title:
--   Rel: slice fibre
-- statement:
--   The Rel construction uses the slice fibre property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L459-L493
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L459-L493

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

theorem GlobalTheory.SmallExtLift.Rel.slice_fibre (H : Rel p ε M V j hj u α) (hε : ε * ε = 0) (h0 : ε ≠ 0)
    [X.IsSeparated] (hV : ⨆ a, V a = ⊤)
    (hA : ∀ a, IsAffineOpen (V a)) {A A' Ak : Scheme.{0}} (s : A ⟶ X) [IsAffineHom s]
    [Flat (s ≫ p)] {π : A' ⟶ A} {f' : A' ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))}
    (P : IsPullback π f' (s ≫ p)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))))
    (hf : Function.Surjective f'.appTop.hom) (hu : ∀ a, IsUnit (u a))
    (t : LB.Gen (M.pull s)) (ht : t.IsGen) {iA : Ak ⟶ A}
    {fk : Ak ⟶ Spec (CommRingCat.of (IsLocalRing.ResidueField R))}
    (w : iA ≫ s ≫ p = fk ≫ Spec.map (CommRingCat.ofHom (IsLocalRing.residue R)))
    (sk : Ak ⟶ Y) (e : sk ≫ i = iA ≫ s) :
    ∃ ψ : ∀ a, Γ(Ak, sk ⁻¹ᵁ i ⁻¹ᵁ V a), ∀ a b,
      (sk.app (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b)).hom
          ((i.appLE (V a ⊓ V b) (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b) (fun _ h => h)).hom (α a b)) =
        (Ak.presheaf.map (homOfLE (show sk ⁻¹ᵁ (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b) ≤ sk ⁻¹ᵁ i ⁻¹ᵁ V a from
          fun _ h => h.1)).op).hom (ψ a) -
        (Ak.presheaf.map (homOfLE (show sk ⁻¹ᵁ (i ⁻¹ᵁ V a ⊓ i ⁻¹ᵁ V b) ≤ sk ⁻¹ᵁ i ⁻¹ᵁ V b from
          fun _ h => h.2)).op).hom (ψ b) := by sorry
