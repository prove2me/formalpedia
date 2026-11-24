-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_conductor_ne_bot
-- name    : GroundTheory.Global.IdeleGroup.conductor_ne_bot
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:38:26.2962+00:00
-- url     : https://prove2.me/theorems/b342df95-0e6a-4d0a-8375-78f9484194a8
-- title:
--   Idele Group: conductor ne bot
-- statement:
--   The Idele Group construction uses the conductor ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ConductorIdeal.lean#L99-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ConductorIdeal.lean#L99-L100

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
omit [TopologicalSpace H]

theorem GroundTheory.Global.IdeleGroup.conductor_ne_bot (χ : (FiniteAdeleRing (𝓞 K) K)ˣ →* H) : conductor χ ≠ ⊥ := by sorry
