-- Prove2me | Theorems.Thm_GlobalTheory_TorsorUnit_exists_homogeneous
-- name    : GlobalTheory.TorsorUnit.exists_homogeneous
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:46.556837+00:00
-- url     : https://prove2.me/theorems/39c4266e-95b1-4a63-bc55-3fc9d2f38f11
-- title:
--   Torsor Unit: exists homogeneous
-- statement:
--   The Torsor Unit construction uses the exists homogeneous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLocalUnitOfWeight.lean#L121-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/ExistsLocalUnitOfWeight.lean#L121-L185

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsLocalUnitOfWeight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.TorsorUnit
variable {X : Type} [AddCommGroup X] {A C R R' : Type} [CommRing A] [CommRing C] [CommRing R]
  [CommRing R']

theorem GlobalTheory.TorsorUnit.exists_homogeneous {α : A →+* C} (hα : α.FaithfullyFlat) {ρ : C →+* AddMonoidAlgebra C X}
    (h : ∀ (R : Type) [CommRing R], IsTorsorOn R α ρ) (χ : X) (p : Ideal A) (hp : p ≠ ⊤) :
    ∃ a ∉ p, ∃ c c' : C, c * c' = α a ∧ ρ c = AddMonoidAlgebra.single χ c := by sorry
