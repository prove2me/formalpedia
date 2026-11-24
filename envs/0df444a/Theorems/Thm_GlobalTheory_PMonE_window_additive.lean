-- Prove2me | Theorems.Thm_GlobalTheory_PMonE_window_additive
-- name    : GlobalTheory.PMonE.window_additive
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T18:40:05.257994+00:00
-- url     : https://prove2.me/theorems/7caf4f27-be99-4b99-a3cf-cf7739811c12
-- title:
--   PMon E: window additive
-- statement:
--   The PMon E construction uses the window additive property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WindowAdditive.lean#L5-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/WindowAdditive.lean#L5-L34

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_WindowAdditive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PMonE

theorem GlobalTheory.PMonE.window_additive (q : ℝ) (hq : 2 ≤ q) (r : ℤ) (α f : ℤ → ℝ) (hα : Antitone α)
    (hf : ∀ J, f (J + 1) - f J = (α J - α (J + 1)) * (q ^ (r - J) - 1)) :
    (∀ J, J ≤ r → f J + α J ≤ f r + α r) ∧
    (∀ J, r + 1 ≤ J → f J - α J / 2 ≤ f r - α (r + 1) / 2) := by sorry
