-- Prove2me | Theorems.Thm_GroundTheory_Global_rationalPrimeUnder_le_absNorm
-- name    : GroundTheory.Global.rationalPrimeUnder_le_absNorm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:17.250092+00:00
-- url     : https://prove2.me/theorems/1f28e385-1cba-47e8-92be-34cb03b55dce
-- title:
--   Global: rational Prime Under le abs Norm
-- statement:
--   The Global construction uses the rational Prime Under le abs Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/DegreeOnePrimes.lean#L45-L48

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

theorem GroundTheory.Global.rationalPrimeUnder_le_absNorm (w : HeightOneSpectrum (𝓞 L)) :
    rationalPrimeUnder w ≤ Ideal.absNorm w.asIdeal := by sorry
