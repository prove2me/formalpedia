-- Prove2me | Theorems.Thm_GlobalTheory_LimitSeriesPowSmul_target
-- name    : GlobalTheory.LimitSeriesPowSmul.target
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:04:43.29214+00:00
-- url     : https://prove2.me/theorems/84cd94df-7f4a-4b4a-9aac-fd364ec8a0f5
-- title:
--   Limit Series Pow Smul: target
-- statement:
--   The Limit Series Pow Smul construction uses the target property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLimitSeries.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLimitSeries.lean#L20-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLimitSeries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.LimitSeriesPowSmul

theorem GlobalTheory.LimitSeriesPowSmul.target : ∀ {R : Type} [inst : CommRing R] (p : R) [IsPrecomplete (Ideal.span {p}) R]
    (f : ℕ → R), ∃ (L : R), ∀ (k : ℕ), p ^ k ∣ ∑ i ∈ Finset.range k, p ^ i * f i - L := by sorry
