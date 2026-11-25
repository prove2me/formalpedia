-- Prove2me | Theorems.Thm_GroundTheory_Global_primeIdealZetaSum_primesAbove
-- name    : GroundTheory.Global.primeIdealZetaSum_primesAbove
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:14:50.167321+00:00
-- url     : https://prove2.me/theorems/f9babc86-b8e3-4772-9c03-cb2440eebd5c
-- title:
--   Global: prime Ideal Zeta Sum primes Above
-- statement:
--   The Global construction uses the prime Ideal Zeta Sum primes Above property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L218-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L218-L269

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
import Definitions.Def_GroundTheory_GlobalFields_KummerTheory_Splitting
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOneDensity
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
open NumberField IsDedekindDomain Filter Topology Set Ideal
noncomputable section
variable {K : Type*} [Field K] [NumberField K] {L : Type*} [Field L] [NumberField L]
  [Algebra K L]

theorem GroundTheory.Global.primeIdealZetaSum_primesAbove {T : Set (HeightOneSpectrum (𝓞 K))}
    (hT : ∀ v ∈ T, SplitsCompletely L v) {s : ℝ} (hs : 1 < s) :
    (primesAbove L T).primeIdealZetaSum s = Module.finrank K L * T.primeIdealZetaSum s := by sorry
