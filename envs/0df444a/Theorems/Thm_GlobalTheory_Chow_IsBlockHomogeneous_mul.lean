-- Prove2me | Theorems.Thm_GlobalTheory_Chow_IsBlockHomogeneous_mul
-- name    : GlobalTheory.Chow.IsBlockHomogeneous.mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:58:20.601547+00:00
-- url     : https://prove2.me/theorems/70f0f8e2-c0ae-5b92-a4b5-1b49165335eb
-- title:
--   Is Block Homogeneous: mul
-- statement:
--   The Is Block Homogeneous construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L288-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L288-L290

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

theorem GlobalTheory.Chow.IsBlockHomogeneous.mul {f g : MvPolynomial (β × σ) K} {a b : β → ℕ}
    (hf : IsBlockHomogeneous f a) (hg : IsBlockHomogeneous g b) :
    IsBlockHomogeneous (f * g) (a + b) := by sorry
