-- Prove2me | Theorems.Thm_GroundTheory_Global_higherDegreePrimes_subset
-- name    : GroundTheory.Global.higherDegreePrimes_subset
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:30.591385+00:00
-- url     : https://prove2.me/theorems/49c0638d-da17-43e6-a2d7-c2e922d0eb98
-- title:
--   Global: higher Degree Primes subset
-- statement:
--   The Global construction uses the higher Degree Primes subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L170-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L170-L172

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

theorem GroundTheory.Global.higherDegreePrimes_subset :
    higherDegreePrimes K L ⊆ {w : HeightOneSpectrum (𝓞 L) | ¬ (Ideal.absNorm w.asIdeal).Prime} := by sorry
