-- Prove2me | Theorems.Thm_GlobalTheory_Chow_IsBlockHomogeneous_rename
-- name    : GlobalTheory.Chow.IsBlockHomogeneous.rename
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:49:27.360666+00:00
-- url     : https://prove2.me/theorems/ac27d2e6-5b54-479a-a8c9-9fd3e6500f60
-- title:
--   Is Block Homogeneous: rename
-- statement:
--   The Is Block Homogeneous construction uses the rename property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L304-L317
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L304-L317

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

theorem GlobalTheory.Chow.IsBlockHomogeneous.rename [Fintype σ] (e : β ≃ β') {f : MvPolynomial (β × σ) K}
    {a : β → ℕ} (h : IsBlockHomogeneous f a) :
    IsBlockHomogeneous (rename (Prod.map e id) f) (a ∘ e.symm) := by sorry
