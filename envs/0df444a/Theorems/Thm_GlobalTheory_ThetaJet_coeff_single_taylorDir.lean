-- Prove2me | Theorems.Thm_GlobalTheory_ThetaJet_coeff_single_taylorDir
-- name    : GlobalTheory.ThetaJet.coeff_single_taylorDir
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:02:45.501823+00:00
-- url     : https://prove2.me/theorems/ef5825e5-c339-4588-b5ed-9102ab174c59
-- title:
--   Theta Jet: coeff single taylor Dir
-- statement:
--   The Theta Jet construction uses the coeff single taylor Dir property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsTranslateJetNeZero.lean#L185-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsTranslateJetNeZero.lean#L185-L191

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_TBNFinal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_LevelThreeSeparatesTangents
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaValues_MemAnalyticAtZeroOfEventuallyDifferentiableAt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_PredMulSumPadicValNatFactorialAddCardLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsTranslateJetNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ReciprocityTheory.ChartRestriction.G.I2 Filter Topology
open GlobalTheory
open GlobalTheory.ThetaJet
variable {ι : Type} [Fintype ι]

theorem GlobalTheory.ThetaJet.coeff_single_taylorDir {σ W : Type*} [Fintype σ] [NormedAddCommGroup W] [NormedSpace ℂ W]
    (u : σ → W) {F : W → ℂ} (hF : AnalyticAt ℂ F 0) (i : σ) :
    MvPowerSeries.coeff (Finsupp.single i 1) (taylorDir u F) = fderiv ℂ F 0 (u i) := by sorry
