-- Prove2me | Theorems.Thm_GroundTheory_Global_unitsLevel_antitone
-- name    : GroundTheory.Global.unitsLevel_antitone
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:22:54.814862+00:00
-- url     : https://prove2.me/theorems/6f51a797-552a-44ba-bfa8-70a7d0ac048f
-- title:
--   Global: units Level antitone
-- statement:
--   The Global construction uses the units Level antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LocalConductor.lean#L86-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LocalConductor.lean#L86-L90

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

theorem GroundTheory.Global.unitsLevel_antitone : Antitone (unitsLevel (K := K) v) := by sorry
