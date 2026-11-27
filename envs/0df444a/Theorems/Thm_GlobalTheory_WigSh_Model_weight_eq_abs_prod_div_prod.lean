-- Prove2me | Theorems.Thm_GlobalTheory_WigSh_Model_weight_eq_abs_prod_div_prod
-- name    : GlobalTheory.WigSh.Model.weight_eq_abs_prod_div_prod
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:32.510622+00:00
-- url     : https://prove2.me/theorems/11ba8876-06cd-45e0-876c-55c9c42991c3
-- title:
--   Model: weight eq abs prod div prod
-- statement:
--   The Model construction uses the weight eq abs prod div prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/FactorNonneg.lean#L65-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Jets/FactorNonneg.lean#L65-L79

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

theorem GlobalTheory.WigSh.Model.weight_eq_abs_prod_div_prod {n : ℕ} {L : Fin (n + 1) → ℤ} {M : Fin n → ℤ} (h : Box L M) (β : ℝ)
    (u : Fin (n + 1) → ℝ) (ρ : Fin n → ℝ)
    (hu : ∀ j, (L j : ℝ) = u j - (n : ℝ) / 2 - β)
    (hρ : ∀ j, (M j : ℝ) = ρ j - ((n : ℝ) - 1) / 2 - β) (l : Fin (n + 1)) :
    wP L M l = (∏ i, |u l + 1 / 2 - ρ i|) / ∏ i ∈ univ.erase l, |u l - u i| := by sorry
