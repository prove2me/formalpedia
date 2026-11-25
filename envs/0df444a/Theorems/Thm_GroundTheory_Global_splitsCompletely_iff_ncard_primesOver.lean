-- Prove2me | Theorems.Thm_GroundTheory_Global_splitsCompletely_iff_ncard_primesOver
-- name    : GroundTheory.Global.splitsCompletely_iff_ncard_primesOver
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T03:14:58.793821+00:00
-- url     : https://prove2.me/theorems/fccd98b9-f6f2-57de-adae-1a1cdaeddc33
-- title:
--   Global: splits Completely iff ncard primes Over
-- statement:
--   The Global construction uses the splits Completely iff ncard primes Over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L170-L189
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L170-L189

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
variable {K : Type*} [Field K] [NumberField K] (L : Type*) [Field L] [NumberField L] [Algebra K L]

theorem GroundTheory.Global.splitsCompletely_iff_ncard_primesOver (v : HeightOneSpectrum (𝓞 K)) :
    SplitsCompletely L v ↔ (v.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L := by sorry
