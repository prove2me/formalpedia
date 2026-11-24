-- Prove2me | Theorems.Thm_GlobalTheory_NoBasePoint_exists_two_points
-- name    : GlobalTheory.NoBasePoint.exists_two_points
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:52:06.394248+00:00
-- url     : https://prove2.me/theorems/ab35f85d-6cad-4e69-a34a-fd60b05808d5
-- title:
--   No Base Point: exists two points
-- statement:
--   The No Base Point construction uses the exists two points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSecValueIsUnit.lean#L32-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsSecValueIsUnit.lean#L32-L67

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SquareUnits
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueSecEqMulGen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSecValueIsUnit
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
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic ReciprocityTheory.ChartRestriction.G.H1.SquareUnits
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.NoBasePoint
variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem GlobalTheory.NoBasePoint.exists_two_points {K : Type} [Field K] [IsAlgClosed K] (t : Spec (CommRingCat.of K) ⟶ S)
    [LocallyOfFiniteType A.hom] [IsIntegral (Over.mk t ⊗ A).left] (D : (Over.mk t ⊗ A).left.Opens)
    (hD : (D : Set (Over.mk t ⊗ A).left).Nonempty) (x c : Over.mk t ⟶ A) :
    ∃ a : Over.mk t ⟶ A, (∀ p, (ptSecT A (a * x)).left p ∈ D) ∧ ∀ p, (ptSecT A (a⁻¹ * c)).left p ∈ D := by sorry
