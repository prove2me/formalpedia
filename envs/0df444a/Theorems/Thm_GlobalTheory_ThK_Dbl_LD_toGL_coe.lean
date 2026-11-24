-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_toGL_coe
-- name    : GlobalTheory.ThK.Dbl.LD.toGL_coe
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:03:37.043623+00:00
-- url     : https://prove2.me/theorems/d3c048e2-e253-43d6-976d-a4c3d523554c
-- title:
--   LD: to GL coe
-- statement:
--   The LD construction uses the to GL coe property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistE.lean#L26-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistE.lean#L26-L26

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

theorem GlobalTheory.ThK.Dbl.LD.toGL_coe (x : GL (Fin d) k) : toGL x.1 = x := by sorry
