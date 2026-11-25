-- Prove2me | Theorems.Thm_GlobalTheory_PushChart_isUnivJ_comp
-- name    : GlobalTheory.PushChart.isUnivJ_comp
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T03:00:38.552325+00:00
-- url     : https://prove2.me/theorems/199b991e-00c0-5890-8400-b067c82eb77d
-- title:
--   Push Chart: is Univ J comp
-- statement:
--   The Push Chart construction uses the is Univ J comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/PushChart.lean#L32-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FormalGroupCharts/PushChart.lean#L32-L46

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwoChartAtlas_AdditionLawSecondIdentity
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_ExistsGroupIsoCubicalIsoOfTripleMapIdStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FormalGroupCharts_PushChart
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.TB (dLin transF IsInvPair dAct)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ChartCmp
open GlobalTheory GlobalTheory.PushChart

theorem GlobalTheory.PushChart.isUnivJ_comp {V : Type} [CommRing V] {G G' : Over (Sp V)} [GrpObj G] [GrpObj G'] (ψ : G ≅ G') [IsMonHom ψ.hom]
    {κ : Type} {z : GlobalTheory.PowGerm.JetPts G κ} (h : GlobalTheory.PowGerm.IsUnivJ G κ z) :
    GlobalTheory.PowGerm.IsUnivJ G' κ (fun m => z m ≫ ψ.hom) := by sorry
