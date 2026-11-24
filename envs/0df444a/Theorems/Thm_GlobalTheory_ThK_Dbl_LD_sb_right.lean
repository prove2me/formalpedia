-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_right
-- name    : GlobalTheory.ThK.Dbl.LD.sb_right
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:14.720238+00:00
-- url     : https://prove2.me/theorems/29b8fc0e-2ed2-4454-8a68-0edea9570cf5
-- title:
--   LD: sb right
-- statement:
--   The LD construction uses the sb right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistC.lean#L94-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistC.lean#L94-L96

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistC
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
variable {k : Type} [Field k] {n d : ℕ}
variable [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k]

theorem GlobalTheory.ThK.Dbl.LD.sb_right {m : Type} {φ : Matrix m (Fin d) k → ℂ} (hφ : φ ∈ SB _) {h : Matrix (Fin d) (Fin d) k} (hh : h.det ≠ 0) :
    (fun y => φ (y * h)) ∈ SB (Matrix m (Fin d) k) := by sorry
