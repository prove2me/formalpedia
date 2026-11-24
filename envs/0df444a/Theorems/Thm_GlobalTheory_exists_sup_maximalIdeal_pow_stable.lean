-- Prove2me | Theorems.Thm_GlobalTheory_exists_sup_maximalIdeal_pow_stable
-- name    : GlobalTheory.exists_sup_maximalIdeal_pow_stable
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:42:22.206737+00:00
-- url     : https://prove2.me/theorems/1e209253-86a4-4c72-bd1a-ac9e08b7db43
-- title:
--   Global Theory: exists sup maximal Ideal pow stable
-- statement:
--   The Global Theory construction uses the exists sup maximal Ideal pow stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L342-L368
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ExistsBasicOpenEqZeroOfMemIInfPowSmul.lean#L342-L368

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

theorem GlobalTheory.exists_sup_maximalIdeal_pow_stable [IsNoetherianRing R] [IsLocalRing R]
    (J : ℕ → Ideal R) (hJ : Antitone J) (k : ℕ) :
    ∃ m, ∀ m' ≥ m, J m' ⊔ maximalIdeal R ^ k = J m ⊔ maximalIdeal R ^ k := by sorry
