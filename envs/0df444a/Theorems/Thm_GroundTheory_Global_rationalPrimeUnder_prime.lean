-- Prove2me | Theorems.Thm_GroundTheory_Global_rationalPrimeUnder_prime
-- name    : GroundTheory.Global.rationalPrimeUnder_prime
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:49.609826+00:00
-- url     : https://prove2.me/theorems/9a7139dd-3303-4e6a-85b9-d6f0b3f895f2
-- title:
--   Global: rational Prime Under prime
-- statement:
--   The Global construction uses the rational Prime Under prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L32-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L32-L33

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
omit [NumberField L]

theorem GroundTheory.Global.rationalPrimeUnder_prime (w : HeightOneSpectrum (𝓞 L)) : (rationalPrimeUnder w).Prime := by sorry
