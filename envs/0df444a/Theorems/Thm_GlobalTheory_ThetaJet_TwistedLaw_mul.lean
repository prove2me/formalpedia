-- Prove2me | Theorems.Thm_GlobalTheory_ThetaJet_TwistedLaw_mul
-- name    : GlobalTheory.ThetaJet.TwistedLaw.mul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T16:02:09.584791+00:00
-- url     : https://prove2.me/theorems/5f26814d-144f-4228-b55f-036226daab65
-- title:
--   Twisted Law: mul
-- statement:
--   The Twisted Law construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsTranslateJetNeZero.lean#L98-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/ExistsTranslateJetNeZero.lean#L98-L110

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

theorem GlobalTheory.ThetaJet.TwistedLaw.mul {Y : GT ι} {k l : ℕ} {c d : EuclideanSpace ℂ ι}
    {F G : EuclideanSpace ℂ ι → ℂ} (hF : TwistedLaw Y k c F) (hG : TwistedLaw Y l d G) :
    TwistedLaw Y (k + l) (c + d) (F * G) := by sorry
