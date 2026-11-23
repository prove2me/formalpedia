-- Prove2me | Theorems.Thm_GlobalTheory_Chow_IsBlockHomogeneous_unique
-- name    : GlobalTheory.Chow.IsBlockHomogeneous.unique
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:13:33.216463+00:00
-- url     : https://prove2.me/theorems/47b6f4b5-c432-4afa-bb0b-e911df16aaa4
-- title:
--   Is Block Homogeneous: unique
-- statement:
--   The Is Block Homogeneous construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L292-L294
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/ThetaMetrics/WeightedHomogeneousComponentMemElimIdeal.lean#L292-L294

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

theorem GlobalTheory.Chow.IsBlockHomogeneous.unique {f : MvPolynomial (β × σ) K} {a b : β → ℕ} (h : f ≠ 0)
    (ha : IsBlockHomogeneous f a) (hb : IsBlockHomogeneous f b) : a = b := by sorry
