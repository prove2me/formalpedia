-- Prove2me | Theorems.Thm_GroundTheory_Global_isOpen_ker_of_noSmallSubgroups
-- name    : GroundTheory.Global.isOpen_ker_of_noSmallSubgroups
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:57:18.116084+00:00
-- url     : https://prove2.me/theorems/d84c00b2-5345-43de-95c5-2cac6b0bb363
-- title:
--   Global: is Open ker of no Small Subgroups
-- statement:
--   The Global construction uses the is Open ker of no Small Subgroups property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L100-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/NoSmallSubgroups.lean#L100-L111

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

theorem GroundTheory.Global.isOpen_ker_of_noSmallSubgroups
    (hG : ∀ W ∈ 𝓝 (1 : G), ∃ V : OpenSubgroup G, (V : Set G) ⊆ W) (hH : NoSmallSubgroups H)
    (f : G →* H) (hf : Continuous f) : IsOpen (f.ker : Set G) := by sorry
