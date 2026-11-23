-- Prove2me | Theorems.Thm_GlobalTheory_ThickeningClosed_mem_of_thickenings
-- name    : GlobalTheory.ThickeningClosed.mem_of_thickenings
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:35:19.505633+00:00
-- url     : https://prove2.me/theorems/77cd971e-94d2-46bb-8ace-dd7ac999f90e
-- title:
--   Thickening Closed: mem of thickenings
-- statement:
--   The Thickening Closed construction uses the mem of thickenings property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoOfIsClosedImmersionOfThickenings.lean#L84-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoOfIsClosedImmersionOfThickenings.lean#L84-L168

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoOfIsClosedImmersionOfThickenings
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.ThickeningClosed
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.ThickeningClosed.mem_of_thickenings {R : Type} [CommRing R] (I : Ideal R)
    {X Z : Scheme.{0}} [IsLocallyNoetherian X] (f : X ⟶ Spec (CommRingCat.of R)) (ι : Z ⟶ X)
    (h : ∀ n : ℕ, ∃ l : pullback f (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I n) ⟶ Z, l ≫ ι = pullback.fst f (_root_.ReciprocityTheory.ChartRestriction.G.Out.thick R I n))
    (x : X) (hx : I ≤ (f x).asIdeal) : x ∈ _root_.GlobalTheory.ThickeningClosed.zeroLocusOpen ι.ker := by sorry
