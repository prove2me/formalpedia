-- Prove2me | Theorems.Thm_GlobalTheory_IsolPt_isArtinianRing_of_finite_points
-- name    : GlobalTheory.IsolPt.isArtinianRing_of_finite_points
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:22:27.884238+00:00
-- url     : https://prove2.me/theorems/00f364dc-67e9-47bc-9000-b0d242ab0161
-- title:
--   Isol Pt: is Artinian Ring of finite points
-- statement:
--   The Isol Pt construction uses the is Artinian Ring of finite points property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsUniversalThickening.lean#L16-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/ExistsUniversalThickening.lean#L16-L41

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegUnif
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasChartsOfForallIsAffineOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsUniversalThickening
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.IsolPt

theorem GlobalTheory.IsolPt.isArtinianRing_of_finite_points (k B : Type) [Field k] [CommRing B] [Algebra k B]
    [Algebra.FiniteType k B] [Finite (B →ₐ[k] AlgebraicClosure k)] : IsArtinianRing B := by sorry
