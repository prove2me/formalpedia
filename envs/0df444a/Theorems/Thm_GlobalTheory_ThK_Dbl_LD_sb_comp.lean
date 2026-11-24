-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_comp
-- name    : GlobalTheory.ThK.Dbl.LD.sb_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:09:27.545159+00:00
-- url     : https://prove2.me/theorems/30fdacc2-ac2b-4282-ac62-72fc21d36474
-- title:
--   LD: sb comp
-- statement:
--   The LD construction uses the sb comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistA.lean#L28-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistA.lean#L28-L32

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

theorem GlobalTheory.ThK.Dbl.LD.sb_comp {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] (e : X → Y) (r : Y → X)
    (ce : Continuous e) (cr : Continuous r) (hre : ∀ x, r (e x) = x) {F : Y → ℂ} (hF : F ∈ SB Y) :
    (fun x => F (e x)) ∈ SB X := by sorry
