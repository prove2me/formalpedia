-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_ind_mem
-- name    : GlobalTheory.ThK.Dbl.LD.ind_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:29.887845+00:00
-- url     : https://prove2.me/theorems/1e8e0739-b59a-472d-adc5-600d40cc0ad9
-- title:
--   LD: ind mem
-- statement:
--   The LD construction uses the ind mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistB.lean#L12-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistB.lean#L12-L14

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

theorem GlobalTheory.ThK.Dbl.LD.ind_mem {K : Subgroup G} (ho : IsOpen (K : Set G)) (hc : IsCompact (K : Set G)) : ind K ∈ SB G := by sorry
