-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_valuation_sub_le_one
-- name    : GroundTheory.Global.exists_valuation_sub_le_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:41:05.479886+00:00
-- url     : https://prove2.me/theorems/e5bd3ff1-5f94-46e8-9b58-51b3a90f01d0
-- title:
--   Global: exists valuation sub le one
-- statement:
--   The Global construction uses the exists valuation sub le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Approximation.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Adele/Approximation.lean#L12-L15

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsValuationSubLeOne
import Definitions.Def_GroundTheory_GlobalFields_Adele_Approximation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open scoped RestrictedProduct
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem GroundTheory.Global.exists_valuation_sub_le_one (S : Finset (HeightOneSpectrum R))
    (x : HeightOneSpectrum R → K) :
    ∃ k : K, (∀ v ∈ S, v.valuation K (k - x v) ≤ 1) ∧ (∀ v ∉ S, v.valuation K k ≤ 1) := by sorry
