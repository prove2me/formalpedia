-- Prove2me | Theorems.Thm_GlobalTheory_GramSubmodular_gram_det_re_nonneg
-- name    : GlobalTheory.GramSubmodular.gram_det_re_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:35:57.08135+00:00
-- url     : https://prove2.me/theorems/d1fb2e76-e170-4035-acc6-fa6384343112
-- title:
--   Gram Submodular: gram det re nonneg
-- statement:
--   The Gram Submodular construction uses the gram det re nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/GramDetFromColsEqZero.lean#L13-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TorusHaarMeasure/GramDetFromColsEqZero.lean#L13-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TorusHaarMeasure_GramDetFromColsEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology Matrix
open scoped ComplexOrder ENNReal Pointwise
open GlobalTheory
open GlobalTheory.GramSubmodular
variable {m α β γ : Type} [Fintype m] [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem GlobalTheory.GramSubmodular.gram_det_re_nonneg (U : Matrix m α ℂ) : 0 ≤ (Uᴴ * U).det.re := by sorry
