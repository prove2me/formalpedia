-- Prove2me | Theorems.Thm_GlobalTheory_Chow_weightedHomogeneousComponent_mem_elimIdeal
-- name    : GlobalTheory.Chow.weightedHomogeneousComponent_mem_elimIdeal
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:21.188272+00:00
-- url     : https://prove2.me/theorems/9bd4fa4c-f5df-49c7-bb23-64f6c6a65209
-- title:
--   Chow: weighted Homogeneous Component mem elim Ideal
-- statement:
--   The Chow construction uses the weighted Homogeneous Component mem elim Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L343-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L343-L360

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
variable {K : Type*} [CommRing K] {σ β β' : Type*}
variable [DecidableEq β] [DecidableEq β']

theorem GlobalTheory.Chow.weightedHomogeneousComponent_mem_elimIdeal [Fintype σ] [Finite β]
    {p : Ideal (MvPolynomial σ K)}
    {f : MvPolynomial (β × σ) K} (hf : f ∈ elimIdeal β p) (a : β → ℕ) :
    weightedHomogeneousComponent blockWeight a f ∈ elimIdeal β p := by sorry
