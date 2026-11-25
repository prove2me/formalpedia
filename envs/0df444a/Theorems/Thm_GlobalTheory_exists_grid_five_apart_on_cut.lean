-- Prove2me | Theorems.Thm_GlobalTheory_exists_grid_five_apart_on_cut
-- name    : GlobalTheory.exists_grid_five_apart_on_cut
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:45:30.370655+00:00
-- url     : https://prove2.me/theorems/7721c1ba-09e7-4256-bc82-6d5abfbd9df9
-- title:
--   Global Theory: exists grid five apart on cut
-- statement:
--   The Global Theory construction uses the exists grid five apart on cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGridFiveApartOnCut.lean#L8-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/ExistsGridFiveApartOnCut.lean#L8-L45

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_StatementM
import Definitions.Def_Formalism_HermitianCurvature_StatementI
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_ExistsGridFiveApartOnCut
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt Finset
open GlobalTheory

theorem GlobalTheory.exists_grid_five_apart_on_cut :
    (∀ (u u' : ℕ → ℝ) (l M₀ : ℕ), 5 * (M₀ : ℝ) ≤ |u l - u' l| → ∃ Y : Finset ℝ, M₀ ≤ Y.card ∧
      (∀ y ∈ Y, ∀ y' ∈ Y, y ≠ y' → 5 ≤ |y - y'|) ∧
      ∀ y ∈ Y, I.OnCut u u' l y ∧ I.OnCut u u' l (y + 1)) ∧
    ∀ r : ℕ, 5 * (3 * (r + 1) * (2 * r + 1)) ≤ 30 * (r + 1) ^ 2 + 6 := by sorry
