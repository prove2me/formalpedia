-- Prove2me | Theorems.Thm_GlobalTheory_ThickeningClosed_noZeroDivisors_fiber
-- name    : GlobalTheory.ThickeningClosed.noZeroDivisors_fiber
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:49:15.76355+00:00
-- url     : https://prove2.me/theorems/2a64cd0f-cc74-41a9-8673-5a5c91ecdbe7
-- title:
--   Thickening Closed: no Zero Divisors fiber
-- statement:
--   The Thickening Closed construction uses the no Zero Divisors fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoOfIsClosedImmersionOfThickenings.lean#L174-L198
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoOfIsClosedImmersionOfThickenings.lean#L174-L198

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

theorem GlobalTheory.ThickeningClosed.noZeroDivisors_fiber {R C : Type} [CommRing R] [CommRing C]
    [Algebra R C] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (j : Spec (CommRingCat.of C) ⟶ X) [IsOpenImmersion j]
    (hj : Spec.map (CommRingCat.ofHom (algebraMap R C)) = j ≫ f)
    (p : PrimeSpectrum R) [IsIntegral (f.fiber p)] : NoZeroDivisors (p.asIdeal.Fiber C) := by sorry
