-- Prove2me | Theorems.Thm_GroundTheory_Global_two_le_absNorm_of_prime
-- name    : GroundTheory.Global.two_le_absNorm_of_prime
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:36:26.857809+00:00
-- url     : https://prove2.me/theorems/6c02ef3d-72f7-4ba1-bbb9-bfa3ea46ea9e
-- title:
--   Global: two le abs Norm of prime
-- statement:
--   The Global construction uses the two le abs Norm of prime property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L96-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/PrimeZetaPole.lean#L96-L103

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_DegreeOnePrimes
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_PrimeZetaPole
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
variable (K : Type*) [Field K] [NumberField K]
variable {K}

theorem GroundTheory.Global.two_le_absNorm_of_prime {p : Ideal (𝓞 K)} (hp : Prime p) : 2 ≤ absNorm p := by sorry
