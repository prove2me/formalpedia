-- Prove2me | Theorems.Thm_GlobalTheory_posDef_quad_margin
-- name    : GlobalTheory.posDef_quad_margin
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:13:57.011084+00:00
-- url     : https://prove2.me/theorems/7009be8d-1c28-432c-9caa-88aba7044047
-- title:
--   Global Theory: pos Def quad margin
-- statement:
--   The Global Theory construction uses the pos Def quad margin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PosDefQuadMargin.lean#L31-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PosDefQuadMargin.lean#L31-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PosDefQuadMargin
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.posDef_quad_margin {ι : Type} [Fintype ι] (M : ι → ι → ℝ)
    (hM : ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * M i j) :
    ∃ η : ℝ, 0 < η ∧ ∀ E : ι → ι → ℝ, (∀ i j, |E i j| ≤ η) →
      ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * (M i j + E i j) := by sorry
