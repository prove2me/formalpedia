-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_sb_chR
-- name    : GlobalTheory.ThK.Dbl.LD.sb_chR
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:03:16.229742+00:00
-- url     : https://prove2.me/theorems/21b1c314-cd90-435c-afe7-29e0d8eeab1e
-- title:
--   LD: sb ch R
-- statement:
--   The LD construction uses the sb ch R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistC.lean#L116-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistC.lean#L116-L121

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

theorem GlobalTheory.ThK.Dbl.LD.sb_chR {φ : Matrix (Fin (n + 1)) (Fin (d + 1)) k → ℂ} (hφ : φ ∈ SB _) (h0 : ∀ X, X 0 0 = 0 → φ X = 0) :
    (fun y => φ (chR y)) ∈ SB (((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k) := by sorry
