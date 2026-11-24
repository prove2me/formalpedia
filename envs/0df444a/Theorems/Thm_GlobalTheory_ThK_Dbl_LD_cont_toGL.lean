-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_cont_toGL
-- name    : GlobalTheory.ThK.Dbl.LD.cont_toGL
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:03:15.367322+00:00
-- url     : https://prove2.me/theorems/4c8ceabd-1d8e-498a-a289-1bd850ce683d
-- title:
--   LD: cont to GL
-- statement:
--   The LD construction uses the cont to GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistE.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistE.lean#L28-L35

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

theorem GlobalTheory.ThK.Dbl.LD.cont_toGL : ContinuousOn (toGL (k := k) (d := d)) {X | X.det ≠ 0} := by sorry
