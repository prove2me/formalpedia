-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_left
-- name    : GlobalTheory.ThK.Dbl.LD.sb_left
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:03:31.319328+00:00
-- url     : https://prove2.me/theorems/ac519162-5043-4f07-97f9-18fa534ffdc3
-- title:
--   LD: sb left
-- statement:
--   The LD construction uses the sb left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistE.lean#L102-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistE.lean#L102-L104

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistB
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistD
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology GlobalTheory.WeilM Matrix
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k] {d : ℕ}
variable [NonarchimedeanAddGroup k] [LocallyCompactSpace k]

theorem GlobalTheory.ThK.Dbl.LD.sb_left {φ : Matrix (Fin d) (Fin d) k → ℂ} (hφ : φ ∈ SB _) (g : GL (Fin d) k) :
    (fun y => φ (g.1 * y)) ∈ SB (Matrix (Fin d) (Fin d) k) := by sorry
