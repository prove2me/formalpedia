-- Prove2me | Theorems.Thm_GlobalTheory_Cartier_isRegularFn_of_locally
-- name    : GlobalTheory.Cartier.isRegularFn_of_locally
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:06.233378+00:00
-- url     : https://prove2.me/theorems/5cd595ae-16da-4ff8-8338-56c064f42030
-- title:
--   Cartier: is Regular Fn of locally
-- statement:
--   The Cartier construction uses the is Regular Fn of locally property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L105-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L105-L111

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

theorem GlobalTheory.Cartier.isRegularFn_of_locally {U : X.Opens} {a : Γ(X, U)}
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧ IsRegularFn (resG X hV a)) :
    IsRegularFn a := by sorry
