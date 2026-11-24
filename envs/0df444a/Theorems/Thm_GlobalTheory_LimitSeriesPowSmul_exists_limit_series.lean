-- Prove2me | Theorems.Thm_GlobalTheory_LimitSeriesPowSmul_exists_limit_series
-- name    : GlobalTheory.LimitSeriesPowSmul.exists_limit_series
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:04:25.236264+00:00
-- url     : https://prove2.me/theorems/a7161912-63c6-4d27-8f9d-d51ff37617e4
-- title:
--   Limit Series Pow Smul: exists limit series
-- statement:
--   The Limit Series Pow Smul construction uses the exists limit series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLimitSeries.lean#L9-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLimitSeries.lean#L9-L18

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

theorem GlobalTheory.LimitSeriesPowSmul.exists_limit_series {R : Type} [CommRing R] (p : R) [IsPrecomplete (Ideal.span {p}) R]
    (f : ℕ → R) : ∃ (L : R), ∀ (k : ℕ), p ^ k ∣ ∑ i ∈ Finset.range k, p ^ i * f i - L := by sorry
