-- Prove2me | Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_dvd_of_germ
-- name    : GlobalTheory.Cartier.IsRegularFn.dvd_of_germ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:51.223357+00:00
-- url     : https://prove2.me/theorems/5b4348e8-0b5d-4748-9829-4e210685daeb
-- title:
--   Is Regular Fn: dvd of germ
-- statement:
--   The Is Regular Fn construction uses the dvd of germ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L151-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/IsRegularFnIffOfIsAffineOpen.lean#L151-L183

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

theorem GlobalTheory.Cartier.IsRegularFn.dvd_of_germ {U : X.Opens} {a b : Γ(X, U)} (ha : IsRegularFn a)
    (h : ∀ x (hx : x ∈ U), (X.presheaf.germ U x hx).hom a ∣ (X.presheaf.germ U x hx).hom b) :
    a ∣ b := by sorry
