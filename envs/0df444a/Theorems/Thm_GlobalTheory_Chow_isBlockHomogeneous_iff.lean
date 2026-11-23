-- Prove2me | Theorems.Thm_GlobalTheory_Chow_isBlockHomogeneous_iff
-- name    : GlobalTheory.Chow.isBlockHomogeneous_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:12:31.287409+00:00
-- url     : https://prove2.me/theorems/504745dd-10b2-446c-be5c-5844baee15f4
-- title:
--   Chow: is Block Homogeneous iff
-- statement:
--   The Chow construction uses the is Block Homogeneous iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L283-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L283-L286

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

theorem GlobalTheory.Chow.isBlockHomogeneous_iff [Fintype σ] {f : MvPolynomial (β × σ) K} {a : β → ℕ} :
    IsBlockHomogeneous f a ↔ ∀ d ∈ f.support, ∀ i, ∑ j, d (i, j) = a i := by sorry
