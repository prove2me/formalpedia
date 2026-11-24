-- Prove2me | Theorems.Thm_GroundTheory_Global_not_prime_absNorm_of_mem_higherDegreePrimes
-- name    : GroundTheory.Global.not_prime_absNorm_of_mem_higherDegreePrimes
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:42:18.60269+00:00
-- url     : https://prove2.me/theorems/9af87349-4650-4689-9269-0b6c6a635d6c
-- title:
--   Global: not prime abs Norm of mem higher Degree Primes
-- statement:
--   The Global construction uses the not prime abs Norm of mem higher Degree Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L164-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L164-L168

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
variable (K L) [Field K] [NumberField K] [Algebra K L]
variable {K L}

theorem GroundTheory.Global.not_prime_absNorm_of_mem_higherDegreePrimes {w : HeightOneSpectrum (𝓞 L)}
    (hw : w ∈ higherDegreePrimes K L) : ¬ (Ideal.absNorm w.asIdeal).Prime := by sorry
