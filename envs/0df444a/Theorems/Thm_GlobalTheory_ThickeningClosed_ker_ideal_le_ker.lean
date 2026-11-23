-- Prove2me | Theorems.Thm_GlobalTheory_ThickeningClosed_ker_ideal_le_ker
-- name    : GlobalTheory.ThickeningClosed.ker_ideal_le_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:04:17.967919+00:00
-- url     : https://prove2.me/theorems/f8ac0a22-3d3a-488b-b44f-0402dabc03a3
-- title:
--   Thickening Closed: ker ideal le ker
-- statement:
--   The Thickening Closed construction uses the ker ideal le ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoOfIsClosedImmersionOfThickenings.lean#L18-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsIsoOfIsClosedImmersionOfThickenings.lean#L18-L40

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

theorem GlobalTheory.ThickeningClosed.ker_ideal_le_ker {X Z : Scheme.{0}} (ι : Z ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) {D : CommRingCat.{0}} (ψ : Γ(X, U) ⟶ D) (l : Spec D ⟶ Z)
    (hl : l ≫ ι = Spec.map ψ ≫ hU.fromSpec) :
    ι.ker.ideal ⟨U, hU⟩ ≤ RingHom.ker ψ.hom := by sorry
