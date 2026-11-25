-- Prove2me | Theorems.Thm_GroundTheory_Global_compl_degreeOnePrimes
-- name    : GroundTheory.Global.compl_degreeOnePrimes
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:40:18.048093+00:00
-- url     : https://prove2.me/theorems/3f52c0a3-4c0b-4027-9c5a-b072c111838a
-- title:
--   Global: compl degree One Primes
-- statement:
--   The Global construction uses the compl degree One Primes property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L156-L160
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L156-L160

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

theorem GroundTheory.Global.compl_degreeOnePrimes : (degreeOnePrimes K L)ᶜ = higherDegreePrimes K L := by sorry
