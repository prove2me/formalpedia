-- Prove2me | Theorems.Thm_GlobalTheory_FlagVolume_lintegral_fin_succ
-- name    : GlobalTheory.FlagVolume.lintegral_fin_succ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:46:10.508686+00:00
-- url     : https://prove2.me/theorems/e1356bba-4e4a-46a8-8fc4-9b8b07e57d3b
-- title:
--   Flag Volume: lintegral fin succ
-- statement:
--   The Flag Volume construction uses the lintegral fin succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralProdPartialSums.lean#L59-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/LintegralProdPartialSums.lean#L59-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LintegralProdPartialSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real Set Filter Topology
open scoped ENNReal Nat
open GlobalTheory GlobalTheory.FlagVolume

theorem GlobalTheory.FlagVolume.lintegral_fin_succ {n : ℕ} {f : (Fin (n + 1) → ℂ) → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ y, f y = ∫⁻ z : ℂ, ∫⁻ w : Fin n → ℂ, f (Fin.cons z w) := by sorry
