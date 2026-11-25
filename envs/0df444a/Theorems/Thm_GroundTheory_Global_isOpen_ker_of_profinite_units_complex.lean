-- Prove2me | Theorems.Thm_GroundTheory_Global_isOpen_ker_of_profinite_units_complex
-- name    : GroundTheory.Global.isOpen_ker_of_profinite_units_complex
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:32.066208+00:00
-- url     : https://prove2.me/theorems/5f171ca8-7c96-4c13-941a-96094fb12f49
-- title:
--   Global: is Open ker of profinite units complex
-- statement:
--   The Global construction uses the is Open ker of profinite units complex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L140-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L140-L142

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_NoSmallSubgroups
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
open Topology Filter
variable {G H : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group H] [TopologicalSpace H]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

theorem GroundTheory.Global.isOpen_ker_of_profinite_units_complex (f : G →* ℂˣ) (hf : Continuous f) :
    IsOpen (f.ker : Set G) := by sorry
