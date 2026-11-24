-- Prove2me | Theorems.Thm_GlobalTheory_ChartBaseChange_push_mul
-- name    : GlobalTheory.ChartBaseChange.push_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:43:01.162884+00:00
-- url     : https://prove2.me/theorems/f3dfa8d8-2198-4793-a122-8b03e470e7ca
-- title:
--   Chart Base Change: push mul
-- statement:
--   The Chart Base Change construction uses the push mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/GermEvalOneStandardPointSelf.lean#L86-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/GermEvalOneStandardPointSelf.lean#L86-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_ChartChg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_GermEvalOneStandardPointSelf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (IsGrpPullback pushHom)
open GlobalTheory.JetSer ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.ChartBaseChange
variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R']
variable {G : Over (Spec (CommRingCat.of R))} [GrpObj G] {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G']
  {π : G'.left ⟶ G.left} (hπ : IsGrpPullback G' G (Spec.map (CommRingCat.ofHom (algebraMap R R'))) π)
  {A : Type} [CommRing A] [Algebra R A] [Algebra R' A] [IsScalarTower R R' A]

theorem GlobalTheory.ChartBaseChange.push_mul (y z : sp (R₀ := R') A ⟶ G') : push hπ (y * z) = push hπ y * push hπ z := by sorry
