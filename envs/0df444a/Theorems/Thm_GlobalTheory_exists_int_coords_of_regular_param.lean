-- Prove2me | Theorems.Thm_GlobalTheory_exists_int_coords_of_regular_param
-- name    : GlobalTheory.exists_int_coords_of_regular_param
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T04:01:57.889632+00:00
-- url     : https://prove2.me/theorems/e6a7eafd-23b9-4029-971d-03064b2bb9d9
-- title:
--   Global Theory: exists int coords of regular param
-- statement:
--   The Global Theory construction uses the exists int coords of regular param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsIntCoordsOfRegularParam.lean#L5-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsIntCoordsOfRegularParam.lean#L5-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsIntCoordsOfRegularParam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_int_coords_of_regular_param (n : ℕ) (u : ℕ → ℝ)
    (h : ∀ i ∈ Finset.Icc 1 n, ∃ N : ℕ, u i - u (i + 1) = (N : ℝ) + 1) :
    ∃ (β : ℂ) (L : Fin (n + 1) → ℤ), StrictAnti L ∧
      (∀ j : Fin (n + 1), (u ((j : ℕ) + 1) : ℂ) - ((n + 1 : ℕ) : ℂ) / 2 + 1 / 2 = β + (L j : ℂ)) ∧
      ∀ i j : Fin (n + 1), (L i : ℝ) - (L j : ℝ) = u ((i : ℕ) + 1) - u ((j : ℕ) + 1) := by sorry
