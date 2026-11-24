-- Prove2me | Theorems.Thm_GroundTheory_Global_summable_absNorm_rpow_neg_of_not_prime
-- name    : GroundTheory.Global.summable_absNorm_rpow_neg_of_not_prime
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:06.740412+00:00
-- url     : https://prove2.me/theorems/96e5b4bd-2189-40d7-8511-229addd7dcf6
-- title:
--   Global: summable abs Norm rpow neg of not prime
-- statement:
--   The Global construction uses the summable abs Norm rpow neg of not prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L119-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L119-L140

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
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
open NumberField IsDedekindDomain Filter Topology Set
noncomputable section
variable {K L : Type*} [Field L] [NumberField L]

theorem GroundTheory.Global.summable_absNorm_rpow_neg_of_not_prime {s : ℝ} (hs : 1 / 2 < s) :
    Summable fun w : {w : HeightOneSpectrum (𝓞 L) // ¬ (Ideal.absNorm w.asIdeal).Prime} =>
      (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-s) := by sorry
