-- Prove2me | Theorems.Thm_GroundTheory_Global_ncard_primesOver_of_splitsCompletely
-- name    : GroundTheory.Global.ncard_primesOver_of_splitsCompletely
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T03:16:17.851307+00:00
-- url     : https://prove2.me/theorems/4ad7db19-c1b1-4344-8cb4-81c9f81b14e0
-- title:
--   Global: ncard primes Over of splits Completely
-- statement:
--   The Global construction uses the ncard primes Over of splits Completely property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L191-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOneDensity.lean#L191-L193

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

theorem GroundTheory.Global.ncard_primesOver_of_splitsCompletely {v : HeightOneSpectrum (𝓞 K)}
    (hv : SplitsCompletely L v) : (v.asIdeal.primesOver (𝓞 L)).ncard = Module.finrank K L := by sorry
