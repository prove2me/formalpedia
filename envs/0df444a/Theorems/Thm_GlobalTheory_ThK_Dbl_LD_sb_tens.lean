-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_tens
-- name    : GlobalTheory.ThK.Dbl.LD.sb_tens
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:18:08.233236+00:00
-- url     : https://prove2.me/theorems/fee1212a-e578-4bed-b8de-55718eb1a486
-- title:
--   LD: sb tens
-- statement:
--   The LD construction uses the sb tens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistA.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistA.lean#L34-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology GlobalTheory.WeilM
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD

theorem GlobalTheory.ThK.Dbl.LD.sb_tens {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y] {f : X → ℂ} {g : Y → ℂ}
    (hf : f ∈ SB X) (hg : g ∈ SB Y) : (fun z : X × Y => f z.1 * g z.2) ∈ SB (X × Y) := by sorry
