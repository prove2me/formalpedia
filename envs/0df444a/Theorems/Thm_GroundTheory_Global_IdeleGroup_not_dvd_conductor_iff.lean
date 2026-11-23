-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_not_dvd_conductor_iff
-- name    : GroundTheory.Global.IdeleGroup.not_dvd_conductor_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:52.66558+00:00
-- url     : https://prove2.me/theorems/d868564b-e78d-4bc6-9b90-d21c1eab9342
-- title:
--   Idele Group: not dvd conductor iff
-- statement:
--   The Idele Group construction uses the not dvd conductor iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ConductorIdeal.lean#L116-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ConductorIdeal.lean#L116-L122

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Conductor
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ConductorIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter NumberField IsDedekindDomain Function
open scoped NumberField.AdeleRing
open GroundTheory GroundTheory.Global
noncomputable section
open GroundTheory.Global.IdeleGroup
variable {K : Type*} [Field K] [NumberField K] {H : Type*} [Group H] [TopologicalSpace H]

theorem GroundTheory.Global.IdeleGroup.not_dvd_conductor_iff (hH : NoSmallSubgroups H) (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H)
    (hχ : Continuous χ) (v : HeightOneSpectrum (𝓞 K)) :
    ¬ v.asIdeal ∣ conductor χ ↔
      (Submonoid.ofClass (v.adicCompletionIntegers K)).units ≤
        (χ.comp (finiteUnitsSingle v)).ker := by sorry
