-- Prove2me | Theorems.Thm_GroundTheory_Global_isOpen_ker_of_continuous
-- name    : GroundTheory.Global.isOpen_ker_of_continuous
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:42:34.188906+00:00
-- url     : https://prove2.me/theorems/48b4d46d-6ee0-477c-8894-9e06a79aae73
-- title:
--   Global: is Open ker of continuous
-- statement:
--   The Global construction uses the is Open ker of continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LocalConductor.lean#L143-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LocalConductor.lean#L143-L146

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
variable {H : Type*} [Group H] [TopologicalSpace H]

theorem GroundTheory.Global.isOpen_ker_of_continuous (hH : NoSmallSubgroups H) (χ : (v.adicCompletion K)ˣ →* H)
    (hχ : Continuous χ) : IsOpen (χ.ker : Set (v.adicCompletion K)ˣ) := by sorry
