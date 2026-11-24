-- Prove2me | Theorems.Thm_GroundTheory_Global_primeIdealZetaSum_higherDegreePrimes_le
-- name    : GroundTheory.Global.primeIdealZetaSum_higherDegreePrimes_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:12.543226+00:00
-- url     : https://prove2.me/theorems/3cd91634-a318-467b-b15e-8f1996bff1eb
-- title:
--   Global: prime Ideal Zeta Sum higher Degree Primes le
-- statement:
--   The Global construction uses the prime Ideal Zeta Sum higher Degree Primes le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L194-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L194-L210

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

theorem GroundTheory.Global.primeIdealZetaSum_higherDegreePrimes_le :
    ∃ C : ℝ, ∀ s : ℝ, 1 ≤ s → (higherDegreePrimes K L).primeIdealZetaSum s ≤ C := by sorry
