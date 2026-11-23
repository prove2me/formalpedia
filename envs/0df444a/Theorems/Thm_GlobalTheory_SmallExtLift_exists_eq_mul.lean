-- Prove2me | Theorems.Thm_GlobalTheory_SmallExtLift_exists_eq_mul
-- name    : GlobalTheory.SmallExtLift.exists_eq_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T03:41:30.944098+00:00
-- url     : https://prove2.me/theorems/323b4192-1d38-44a7-a3cb-c3cf7beca79b
-- title:
--   Small Ext Lift: exists eq mul
-- statement:
--   The Small Ext Lift construction uses the exists eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L223-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsGenOfSmallExtension.lean#L223-L229

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
variable {ε : R} {p : X ⟶ Spec (CommRingCat.of R)}
  {π : Y ⟶ X} {f' : Y ⟶ Spec (CommRingCat.of (R ⧸ Ideal.span {ε}))}

theorem GlobalTheory.SmallExtLift.exists_eq_mul
    (H : IsPullback π f' p (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {ε})))))
    {V : X.Opens} (hV : IsAffineOpen V) (a : Γ(X, V)) (ha : (π.app V).hom a = 0) :
    ∃ b, a = cst p V ε * b := by sorry
