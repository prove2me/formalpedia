-- Prove2me | Theorems.Thm_GlobalTheory_SmallExtLift_Rel_cocycle
-- name    : GlobalTheory.SmallExtLift.Rel.cocycle
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:28.661809+00:00
-- url     : https://prove2.me/theorems/56c5d0ff-ff4e-4cb4-8048-03db8745bd89
-- title:
--   Rel: cocycle
-- statement:
--   The Rel construction uses the cocycle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L297-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L297-L319

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

theorem GlobalTheory.SmallExtLift.Rel.cocycle (H : Rel p ε M V j hj u α) (hε : ε * ε = 0) (hM : M.IsLB)
    (hu : ∀ a, IsUnit (u a)) (a b d : I) (f : Z ⟶ X) (z : Z) (ha : f z ∈ V a) (hb : f z ∈ V b)
    (hd : f z ∈ V d) :
    cstS (f ≫ p) z ε * (gr f z (V a ⊓ V b) ⟨ha, hb⟩ (α a b) + gr f z (V b ⊓ V d) ⟨hb, hd⟩ (α b d) -
      gr f z (V a ⊓ V d) ⟨ha, hd⟩ (α a d)) = 0 := by sorry
