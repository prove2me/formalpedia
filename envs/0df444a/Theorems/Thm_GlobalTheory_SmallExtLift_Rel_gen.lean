-- Prove2me | Theorems.Thm_GlobalTheory_SmallExtLift_Rel_gen
-- name    : GlobalTheory.SmallExtLift.Rel.gen
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:46:26.421807+00:00
-- url     : https://prove2.me/theorems/6ce54b9e-0b28-4494-88e3-1dd0eb821fcd
-- title:
--   Rel: gen
-- statement:
--   The Rel construction uses the gen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L321-L340
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L321-L340

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

theorem GlobalTheory.SmallExtLift.Rel.gen (H : Rel p ε M V j hj u α) (hε : ε * ε = 0) (hM : M.IsLB) (hV : ⨆ a, V a = ⊤)
    (hu : ∀ a, IsUnit (u a)) (β : ∀ a, Γ(X, V a))
    (hβ : ∀ a b x (ha : (𝟙 X : X ⟶ X) x ∈ V a) (hb : (𝟙 X : X ⟶ X) x ∈ V b),
      cstS (𝟙 X ≫ p) x ε * (gr (𝟙 X) x (V a ⊓ V b) ⟨ha, hb⟩ (α a b) -
        (gr (𝟙 X) x _ ha (β a) - gr (𝟙 X) x _ hb (β b))) = 0) :
    ∃ t : LB.Gen M, t.IsGen := by sorry
