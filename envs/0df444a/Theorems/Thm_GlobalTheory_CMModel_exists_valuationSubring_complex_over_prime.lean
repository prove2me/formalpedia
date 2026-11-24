-- Prove2me | Theorems.Thm_GlobalTheory_CMModel_exists_valuationSubring_complex_over_prime
-- name    : GlobalTheory.CMModel.exists_valuationSubring_complex_over_prime
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:04:35.655426+00:00
-- url     : https://prove2.me/theorems/523a3963-788e-43c0-b876-a9105aec3701
-- title:
--   CMModel: exists valuation Subring complex over prime
-- statement:
--   The CMModel construction uses the exists valuation Subring complex over prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsValuationSubringComplexOverPrime.lean#L6-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsValuationSubringComplexOverPrime.lean#L6-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsValuationSubringComplexOverPrime
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMModel

theorem GlobalTheory.CMModel.exists_valuationSubring_complex_over_prime :
    ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F)),
      ∃ V : ValuationSubring ℂ, ∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F := by sorry
