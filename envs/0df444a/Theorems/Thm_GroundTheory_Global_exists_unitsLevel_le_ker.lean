-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_unitsLevel_le_ker
-- name    : GroundTheory.Global.exists_unitsLevel_le_ker
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:01.991214+00:00
-- url     : https://prove2.me/theorems/4175d9db-4a99-4046-8f4f-f74d33e218db
-- title:
--   Global: exists units Level le ker
-- statement:
--   The Global construction uses the exists units Level le ker property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LocalConductor.lean#L134-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/LocalConductor.lean#L134-L141

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

theorem GroundTheory.Global.exists_unitsLevel_le_ker (hH : NoSmallSubgroups H) (χ : (v.adicCompletion K)ˣ →* H)
    (hχ : Continuous χ) : ∃ n : ℕ, 1 ≤ n ∧ unitsLevel v n ≤ χ.ker := by sorry
