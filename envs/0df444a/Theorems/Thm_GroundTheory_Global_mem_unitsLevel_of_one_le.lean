-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_unitsLevel_of_one_le
-- name    : GroundTheory.Global.mem_unitsLevel_of_one_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:46.041805+00:00
-- url     : https://prove2.me/theorems/222da8fc-f72e-459a-992b-ec99612785c8
-- title:
--   Global: mem units Level of one le
-- statement:
--   The Global construction uses the mem units Level of one le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LocalConductor.lean#L57-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LocalConductor.lean#L57-L65

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
variable {v}

theorem GroundTheory.Global.mem_unitsLevel_of_one_le {n : ℕ} (hn : 1 ≤ n) {x : (v.adicCompletion K)ˣ} :
    x ∈ unitsLevel v n ↔ Valued.v ((x : v.adicCompletion K) - 1) ≤ exp (-(n : ℤ)) := by sorry
