-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_Model_wM_eq_abs
-- name    : GlobalTheory.WigSh.Model.wM_eq_abs
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:59.025899+00:00
-- url     : https://prove2.me/theorems/ec94c7e2-1abf-4bf5-9545-453c09457089
-- title:
--   Model: w M eq abs
-- statement:
--   The Model construction uses the w M eq abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/FactorNonneg.lean#L81-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/FactorNonneg.lean#L81-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_Imports
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_FactorNonneg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open GlobalTheory GlobalTheory.WigSh GlobalTheory.WigSh.Model

theorem GlobalTheory.WigSh.Model.wM_eq_abs {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M) (β : ℝ)
    (u : Fin (n + 1) → ℝ) (ρ : Fin n → ℝ)
    (hu : ∀ j, (L j : ℝ) = u j - (n : ℝ) / 2 - β)
    (hρ : ∀ j, (M j : ℝ) = ρ j - ((n : ℝ) - 1) / 2 - β) (l : Fin (n + 1)) :
    wM L M l = (∏ i, |u l - 1 / 2 - ρ i|) / ∏ i ∈ univ.erase l, |u l - u i| := by sorry
