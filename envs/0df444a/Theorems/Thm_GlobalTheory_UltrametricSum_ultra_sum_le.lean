-- Prove2me | Theorems.Thm_GlobalTheory_UltrametricSum_ultra_sum_le
-- name    : GlobalTheory.UltrametricSum.ultra_sum_le
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:23:06.152249+00:00
-- url     : https://prove2.me/theorems/f531aab5-47f4-4081-a92f-940b61eff650
-- title:
--   Ultrametric Sum: ultra sum le
-- statement:
--   The Ultrametric Sum construction uses the ultra sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UltraSumLe.lean#L5-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/UltraSumLe.lean#L5-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UltraSumLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UltrametricSum

theorem GlobalTheory.UltrametricSum.ultra_sum_le {R : Type} [inst : CommRing R] (a : R → ℝ) (h0 : a (0 : R) = (0 : ℝ))
    (hadd : ∀ (x y : R), a (x + y) ≤ Max.max (a x) (a y)) {ι : Type} (s : Finset ι) (f : ι → R)
    (c : ℝ) (hc : (0 : ℝ) ≤ c) (h : ∀ i ∈ s, a (f i) ≤ c) : a (∑ i ∈ s, f i) ≤ c := by sorry
