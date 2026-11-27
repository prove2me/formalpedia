-- Prove2me | Theorems.Thm_GlobalTheory_exists_le_maximalIdeal_pow_of_iInf_eq_bot
-- name    : GlobalTheory.exists_le_maximalIdeal_pow_of_iInf_eq_bot
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:45:25.540435+00:00
-- url     : https://prove2.me/theorems/e3f4b751-4fe0-5afa-b10d-6e04b1757168
-- title:
--   Global Theory: exists le maximal Ideal pow of i Inf eq bot
-- statement:
--   The Global Theory construction uses the exists le maximal Ideal pow of i Inf eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L372-L423
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L372-L423

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsBasicOpenEqZeroOfMemIInfPowSmul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
open GlobalTheory
variable {R : Type*} [CommRing R]
open IsLocalRing

theorem GlobalTheory.exists_le_maximalIdeal_pow_of_iInf_eq_bot [IsNoetherianRing R] [IsLocalRing R]
    [IsPrecomplete (maximalIdeal R) R] (J : ℕ → Ideal R) (hJ : Antitone J) (h0 : ⨅ m, J m = ⊥)
    (k : ℕ) : ∃ m, J m ≤ maximalIdeal R ^ k := by sorry
