-- Prove2me | Theorems.Thm_GlobalTheory_map_maximalIdeal_pow_le
-- name    : GlobalTheory.map_maximalIdeal_pow_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:49:06.851463+00:00
-- url     : https://prove2.me/theorems/6e000f79-0437-5c39-8420-ecfa86741c61
-- title:
--   Global Theory: map maximal Ideal pow le
-- statement:
--   The Global Theory construction uses the map maximal Ideal pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L617-L621
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L617-L621

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
universe u v w
variable (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
  (K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]

theorem GlobalTheory.map_maximalIdeal_pow_le {S O : Type*} [CommRing S] [IsLocalRing S] [CommRing O]
    [IsLocalRing O] (φ : S →+* O) [IsLocalHom φ] (n : ℕ) :
    (maximalIdeal S ^ n).map φ ≤ maximalIdeal O ^ n := by sorry
