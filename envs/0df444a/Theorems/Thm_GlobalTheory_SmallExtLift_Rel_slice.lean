-- Prove2me | Theorems.Thm_GlobalTheory_SmallExtLift_Rel_slice
-- name    : GlobalTheory.SmallExtLift.Rel.slice
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:34.394184+00:00
-- url     : https://prove2.me/theorems/4931a188-17a4-4070-b720-91c236c391e5
-- title:
--   Rel: slice
-- statement:
--   The Rel construction uses the slice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L342-L413
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L342-L413

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
variable {p : X ⟶ Spec (CommRingCat.of R)} {ε : R} {M : LB X} {I : Type} {V : I → X.Opens}
  {j : I → M.ι} {hj : ∀ a, V a ≤ M.U (j a)} {u : ∀ a, Γ(X, V a)} {α : ∀ a b, Γ(X, V a ⊓ V b)}

theorem GlobalTheory.SmallExtLift.Rel.slice (H : Rel p ε M V j hj u α) (hε : ε * ε = 0) (hV : ⨆ a, V a = ⊤)
    (hA : ∀ a, IsAffineOpen (V a)) {A A' : Scheme.{0}} (s : A ⟶ X) [IsAffineHom s]
    {π : A' ⟶ A} {f' : A' ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))}
    (P : IsPullback π f' (s ≫ p)
      (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))))
    (hf : Function.Surjective f'.appTop.hom) (hu : ∀ a, IsUnit (u a))
    (t : LB.Gen (M.pull s)) (ht : t.IsGen) :
    ∃ β : ∀ a, Γ(A, s ⁻¹ᵁ V a), ∀ a b x (ha : s ((𝟙 A : A ⟶ A) x) ∈ V a)
      (hb : s ((𝟙 A : A ⟶ A) x) ∈ V b),
      cstS ((𝟙 A ≫ s) ≫ p) x ε * (gr (𝟙 A ≫ s) x (V a ⊓ V b) ⟨ha, hb⟩ (α a b) -
        (gr (𝟙 A) x (s ⁻¹ᵁ V a) ha (β a) - gr (𝟙 A) x (s ⁻¹ᵁ V b) hb (β b))) = 0 := by sorry
