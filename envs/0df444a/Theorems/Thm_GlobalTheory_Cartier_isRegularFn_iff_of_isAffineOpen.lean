-- Prove2me | Theorems.Thm_GlobalTheory_Cartier_isRegularFn_iff_of_isAffineOpen
-- name    : GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:05.281568+00:00
-- url     : https://prove2.me/theorems/4d7de437-abfd-4952-a205-affe62a3aa04
-- title:
--   Cartier: is Regular Fn iff of is Affine Open
-- statement:
--   The Cartier construction uses the is Regular Fn iff of is Affine Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L113-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L113-L119

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

theorem GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen {U : X.Opens} (hU : IsAffineOpen U) {a : Γ(X, U)} :
    IsRegularFn a ↔ a ∈ nonZeroDivisors Γ(X, U) := by sorry
