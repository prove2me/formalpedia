-- Prove2me | Theorems.Thm_GlobalTheory_NormSquareRamified_dvd_of_mul_sq
-- name    : GlobalTheory.NormSquareRamified.dvd_of_mul_sq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T18:48:45.630302+00:00
-- url     : https://prove2.me/theorems/414c572d-7a70-444a-ae6f-9ac99c744405
-- title:
--   Norm Square Ramified: dvd of mul sq
-- statement:
--   The Norm Square Ramified construction uses the dvd of mul sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsUnitNormOfIsCoprime.lean#L8-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/IsUnitNormOfIsCoprime.lean#L8-L33

import Mathlib
import Definitions.Def_Formalism_LocalRingCardinality_DataHost
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsUnitNormOfIsCoprime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.NormSquareRamified

theorem GlobalTheory.NormSquareRamified.dvd_of_mul_sq {p : ℕ} (hp : p.Prime) {q D : ℤ} (hq : ¬ (p : ℤ) ∣ q) (B : ℚ)
    (h : ((q * p : ℤ) : ℚ) * B ^ 2 = D) : (p : ℤ) ∣ D := by sorry
