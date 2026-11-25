-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_IntegralGermPointData_charZero_closure
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.IntegralGermPointData.charZero_closure
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:09:02.045913+00:00
-- url     : https://prove2.me/theorems/696756b4-9926-46b6-a336-4957f1d560f4
-- title:
--   Integral Germ Point Data: char Zero closure
-- statement:
--   The Integral Germ Point Data construction uses the char Zero closure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/PointDataQ.lean#L129-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/JetGauges/PointDataQ.lean#L129-L132

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_TwoChartSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_OneCHyp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_ExistsWeightBasisFiltration
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExpF
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_JetGauges_PointDataQ
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt FB)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.IntegralGermPointData
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {t : SAB H (Sp V)}
variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]

theorem GlobalTheory.IndefiniteRowSideFullHecke.IntegralGermPointData.charZero_closure (V : Type) [CommRing V] [IsDomain V] [CharZero V] :
    CharZero (AlgebraicClosure (FractionRing V)) := by sorry
