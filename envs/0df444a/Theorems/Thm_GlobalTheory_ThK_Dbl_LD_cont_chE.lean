-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_cont_chE
-- name    : GlobalTheory.ThK.Dbl.LD.cont_chE
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:59.853557+00:00
-- url     : https://prove2.me/theorems/bb41c90c-8f1f-4aa6-af35-4fce252c4c14
-- title:
--   LD: cont ch E
-- statement:
--   The LD construction uses the cont ch E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistC.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistC.lean#L98-L103

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

theorem GlobalTheory.ThK.Dbl.LD.cont_chE : ContinuousOn (chE (k := k) (n := n) (d := d)) {X | X 0 0 ≠ 0} := by sorry
