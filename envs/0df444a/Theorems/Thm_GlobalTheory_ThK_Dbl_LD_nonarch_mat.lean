-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_nonarch_mat
-- name    : GlobalTheory.ThK.Dbl.LD.nonarch_mat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:31:47.9308+00:00
-- url     : https://prove2.me/theorems/cc2a58ae-b79a-4dc9-9cea-3da06ad2b746
-- title:
--   LD: nonarch mat
-- statement:
--   The LD construction uses the nonarch mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistD.lean#L11-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistD.lean#L11-L13

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistC
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistD
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
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [ContinuousInv₀ k] [T2Space k]
  [NonarchimedeanAddGroup k] [LocallyCompactSpace k] {c : k → ℂ} {ϖ : k}

theorem GlobalTheory.ThK.Dbl.LD.nonarch_mat (n d : ℕ) : NonarchimedeanAddGroup (Matrix (Fin n) (Fin d) k) := by sorry
