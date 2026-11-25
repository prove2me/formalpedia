-- Prove2me | Theorems.Thm_GroundTheory_Global_sq_rationalPrimeUnder_le_absNorm
-- name    : GroundTheory.Global.sq_rationalPrimeUnder_le_absNorm
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:01.8333+00:00
-- url     : https://prove2.me/theorems/849979b4-0209-4ffb-94e7-961e98f8a4ba
-- title:
--   Global: sq rational Prime Under le abs Norm
-- statement:
--   The Global construction uses the sq rational Prime Under le abs Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L50-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L50-L59

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

theorem GroundTheory.Global.sq_rationalPrimeUnder_le_absNorm {w : HeightOneSpectrum (𝓞 L)}
    (hw : ¬ (Ideal.absNorm w.asIdeal).Prime) :
    rationalPrimeUnder w ^ 2 ≤ Ideal.absNorm w.asIdeal := by sorry
