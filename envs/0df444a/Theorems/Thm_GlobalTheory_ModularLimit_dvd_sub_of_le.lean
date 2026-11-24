-- Prove2me | Theorems.Thm_GlobalTheory_ModularLimit_dvd_sub_of_le
-- name    : GlobalTheory.ModularLimit.dvd_sub_of_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T18:26:45.266006+00:00
-- url     : https://prove2.me/theorems/5d81d0c4-323b-4c93-a486-48d0baaff98d
-- title:
--   Modular Limit: dvd sub of le
-- statement:
--   The Modular Limit construction uses the dvd sub of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SmodEqIffDvd.lean#L10-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/SmodEqIffDvd.lean#L10-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SmodEqIffDvd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ModularLimit

theorem GlobalTheory.ModularLimit.dvd_sub_of_le {W : Type} [CommRing W] (x : W) (f : ℕ → W)
    (hf : ∀ k : ℕ, x ^ k ∣ f (k + 1) - f k) {m n : ℕ} (hmn : m ≤ n) :
    x ^ m ∣ f n - f m := by sorry
