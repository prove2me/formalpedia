-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_lc_mat
-- name    : GlobalTheory.ThK.Dbl.LD.lc_mat
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:03:30.874242+00:00
-- url     : https://prove2.me/theorems/dd43f9c9-0372-49d3-bb1a-ea2ccf1ebab6
-- title:
--   LD: lc mat
-- statement:
--   The LD construction uses the lc mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistD.lean#L15-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistD.lean#L15-L16

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

theorem GlobalTheory.ThK.Dbl.LD.lc_mat (n d : ℕ) : LocallyCompactSpace (Matrix (Fin n) (Fin d) k) := by sorry
