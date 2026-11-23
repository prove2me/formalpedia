-- Prove2me | Theorems.Thm_GroundTheory_Global_unitsLevel_zero
-- name    : GroundTheory.Global.unitsLevel_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:50.513005+00:00
-- url     : https://prove2.me/theorems/9b48452e-0b43-4d61-ad4a-069ab76ccc86
-- title:
--   Global: units Level zero
-- statement:
--   The Global construction uses the units Level zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LocalConductor.lean#L67-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LocalConductor.lean#L67-L84

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_LocalConductor
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
open Topology Filter IsDedekindDomain WithZero
noncomputable section
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem GroundTheory.Global.unitsLevel_zero :
    unitsLevel (K := K) v 0 = (Submonoid.ofClass (v.adicCompletionIntegers K)).units := by sorry
