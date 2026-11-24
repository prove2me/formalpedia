-- Prove2me | Theorems.Thm_GlobalTheory_Chow_aeval_genericPoint
-- name    : GlobalTheory.Chow.aeval_genericPoint
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:10:14.071421+00:00
-- url     : https://prove2.me/theorems/b555aada-a2d6-4385-93ae-600d04ec3250
-- title:
--   Chow: aeval generic Point
-- statement:
--   The Chow construction uses the aeval generic Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L226-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L226-L231

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsWeaklyRegularMapCAppendMapLinForm
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_WeightedHomogeneousComponentMemElimIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open GlobalTheory GlobalTheory.Chow
variable {σ β : Type*} [Fintype σ]
variable {K : Type*} [CommRing K]
omit [Fintype σ]

theorem GlobalTheory.Chow.aeval_genericPoint (p : Ideal (MvPolynomial σ K)) (g : MvPolynomial σ K) :
    aeval (genericPoint p) g = algebraMap (MvPolynomial σ K ⧸ p) _ (Ideal.Quotient.mk p g) := by sorry
