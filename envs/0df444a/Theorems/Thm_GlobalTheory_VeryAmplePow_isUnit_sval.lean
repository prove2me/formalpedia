-- Prove2me | Theorems.Thm_GlobalTheory_VeryAmplePow_isUnit_sval
-- name    : GlobalTheory.VeryAmplePow.isUnit_sval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:53.480367+00:00
-- url     : https://prove2.me/theorems/37a3bcc0-9501-48e6-8ae6-e5e4b31fe39f
-- title:
--   Very Ample Pow: is Unit sval
-- statement:
--   The Very Ample Pow construction uses the is Unit sval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L229-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L229-L232

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_H1_SectionArithmetic_isUnit_sval

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
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.VeryAmplePow
open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

theorem GlobalTheory.VeryAmplePow.isUnit_sval {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    IsUnit (sval s r z J) ↔ r z ∈ nonzeroLocus s := by sorry
