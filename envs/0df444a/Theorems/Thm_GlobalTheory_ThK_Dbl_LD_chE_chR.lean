-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_chE_chR
-- name    : GlobalTheory.ThK.Dbl.LD.chE_chR
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:03:47.788666+00:00
-- url     : https://prove2.me/theorems/518461e5-9f99-4c72-ba31-1b214fd1afd8
-- title:
--   LD: ch E ch R
-- statement:
--   The LD construction uses the ch E ch R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistC.lean#L47-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistC.lean#L47-L53

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

theorem GlobalTheory.ThK.Dbl.LD.chE_chR (y : ((Fin (n + 1) → k) × (Fin d → k)) × Matrix (Fin n) (Fin d) k) (hy : y.1.1 0 ≠ 0) : chE (chR y) = y := by sorry
