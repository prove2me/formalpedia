-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_map_idealLevel_le_ker_iff
-- name    : GroundTheory.Global.IdeleGroup.map_idealLevel_le_ker_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T23:40:10.561792+00:00
-- url     : https://prove2.me/theorems/e26b2794-d6a1-4a72-89eb-4a0e7b59f659
-- title:
--   Idele Group: map ideal Level le ker iff
-- statement:
--   The Idele Group construction uses the map ideal Level le ker iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ConductorIdeal.lean#L150-L154
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ConductorIdeal.lean#L150-L154

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

theorem GroundTheory.Global.IdeleGroup.map_idealLevel_le_ker_iff (hH : NoSmallSubgroups H) (χ : IdeleGroup K →* H)
    (hχ : Continuous χ) {𝔪 : Ideal (𝓞 K)} (h𝔪 : 𝔪 ≠ ⊥) :
    (idealLevel 𝔪).map ofFinite ≤ χ.ker ↔ conductor (χ.comp ofFinite) ∣ 𝔪 := by sorry
