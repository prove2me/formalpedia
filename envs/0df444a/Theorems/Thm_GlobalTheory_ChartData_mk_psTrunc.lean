-- Prove2me | Theorems.Thm_GlobalTheory_ChartData_mk_psTrunc
-- name    : GlobalTheory.ChartData.mk_psTrunc
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T14:59:46.921701+00:00
-- url     : https://prove2.me/theorems/1110acc8-0617-4fc7-8752-0ef1dcf101d8
-- title:
--   Chart Data: mk ps Trunc
-- statement:
--   The Chart Data construction uses the mk ps Trunc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsIsChartGOfBasis.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsIsChartGOfBasis.lean#L17-L27

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_Divisibility_GeneratorPowers_IntChartCut
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsPtJ
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsIsChartGOfBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (FGLaw)
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.ChartData
open GlobalTheory.ChartJet (Q gen sq_gen)

theorem GlobalTheory.ChartData.mk_psTrunc {S : Type} [CommRing S] {κ : Type} [Fintype κ] [DecidableEq κ] (m : ℕ) (f : MvPowerSeries κ S)
    (hf : MvPowerSeries.constantCoeff f = 0) :
    ChartJet.pj m f = Ideal.Quotient.mk _ (psTrunc m f - MvPolynomial.C (MvPolynomial.constantCoeff (psTrunc m f))) := by sorry
