-- Prove2me | Theorems.Thm_GlobalTheory_Cartier_isRegularFn_iff_ne_zero
-- name    : GlobalTheory.Cartier.isRegularFn_iff_ne_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:17.040462+00:00
-- url     : https://prove2.me/theorems/ab367ae5-78b6-555b-b24e-0baf2f8e7c10
-- title:
--   Cartier: is Regular Fn iff ne zero
-- statement:
--   The Cartier construction uses the is Regular Fn iff ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L134-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L134-L136

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}

theorem GlobalTheory.Cartier.isRegularFn_iff_ne_zero [IsIntegral X] {U : X.Opens} [Nonempty U] {a : Γ(X, U)} :
    IsRegularFn a ↔ a ≠ 0 := by sorry
