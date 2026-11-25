-- Prove2me | Theorems.Thm_GroundTheory_Global_summable_higherDegreePrimes
-- name    : GroundTheory.Global.summable_higherDegreePrimes
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:42:55.090489+00:00
-- url     : https://prove2.me/theorems/5505d56d-cbb8-4eb6-bf10-91cd7a78fb98
-- title:
--   Global: summable higher Degree Primes
-- statement:
--   The Global construction uses the summable higher Degree Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L184-L190
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L184-L190

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
variable (K L)

theorem GroundTheory.Global.summable_higherDegreePrimes {s : ℝ} (hs : 1 / 2 < s) :
    Summable fun w : higherDegreePrimes K L => (Ideal.absNorm w.1.asIdeal : ℝ) ^ (-s) := by sorry
