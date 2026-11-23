-- Prove2me | Theorems.Thm_GlobalTheory_VeryAmplePow_exists_ratio
-- name    : GlobalTheory.VeryAmplePow.exists_ratio
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:56:38.993505+00:00
-- url     : https://prove2.me/theorems/a2a2f199-f74d-4e2f-b347-72c28918eddb
-- title:
--   Very Ample Pow: exists ratio
-- statement:
--   The Very Ample Pow construction uses the exists ratio property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L154-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsUnitIffMem.lean#L154-L181

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_SectionArithmetic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsUnitIffMem
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

theorem GlobalTheory.VeryAmplePow.exists_ratio {Y : Scheme.{0}} {M : LB Y} (s t : LB.Sec M) :
    ∃ ρ : Γ(Y, nonzeroLocus s), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (k : M.ι), r z ∈ nonzeroLocus s → r z ∈ M.U k →
      gs r z _ (t.f k) = gs r z _ ρ * gs r z _ (s.f k) := by sorry
