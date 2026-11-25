-- Prove2me | Theorems.Thm_GlobalTheory_ThetaJet_sub_affine_mem_sq
-- name    : GlobalTheory.ThetaJet.sub_affine_mem_sq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:02:37.312549+00:00
-- url     : https://prove2.me/theorems/6a582b1f-915b-42cb-86ff-8a4fa5b785ee
-- title:
--   Theta Jet: sub affine mem sq
-- statement:
--   The Theta Jet construction uses the sub affine mem sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsTranslateJetNeZero.lean#L193-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsTranslateJetNeZero.lean#L193-L210

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

theorem GlobalTheory.ThetaJet.sub_affine_mem_sq {σ : Type*} [Fintype σ] (x : MvPowerSeries σ ℂ) :
    x - (MvPowerSeries.constantCoeff x • (1 : MvPowerSeries σ ℂ) +
      ∑ i, MvPowerSeries.coeff (Finsupp.single i 1) x • (MvPowerSeries.X i : MvPowerSeries σ ℂ))
      ∈ germIdeal σ ℂ ^ 2 := by sorry
