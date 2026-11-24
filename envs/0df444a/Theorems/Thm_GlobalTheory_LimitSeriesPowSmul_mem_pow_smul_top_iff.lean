-- Prove2me | Theorems.Thm_GlobalTheory_LimitSeriesPowSmul_mem_pow_smul_top_iff
-- name    : GlobalTheory.LimitSeriesPowSmul.mem_pow_smul_top_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:04:37.955103+00:00
-- url     : https://prove2.me/theorems/b2d8d0ef-e3c9-4895-9fbc-ab207bad8a34
-- title:
--   Limit Series Pow Smul: mem pow smul top iff
-- statement:
--   The Limit Series Pow Smul construction uses the mem pow smul top iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLimitSeries.lean#L5-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsLimitSeries.lean#L5-L7

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

theorem GlobalTheory.LimitSeriesPowSmul.mem_pow_smul_top_iff {R : Type} [CommRing R] (p : R) (n : ℕ) (x : R) :
    x ∈ ((Ideal.span {p}) ^ n • (⊤ : Submodule R R)) ↔ p ^ n ∣ x := by sorry
