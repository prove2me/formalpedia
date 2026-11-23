-- Prove2me | Theorems.Thm_GroundTheory_Global_IdeleGroup_continuous_ofFinite
-- name    : GroundTheory.Global.IdeleGroup.continuous_ofFinite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:38.807529+00:00
-- url     : https://prove2.me/theorems/98aae3cd-2b85-416f-aa8f-f35631bed236
-- title:
--   Idele Group: continuous of Finite
-- statement:
--   The Idele Group construction uses the continuous of Finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ConductorIdeal.lean#L127-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/ConductorIdeal.lean#L127-L131

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

theorem GroundTheory.Global.IdeleGroup.continuous_ofFinite : Continuous (ofFinite (K := K)) := by sorry
