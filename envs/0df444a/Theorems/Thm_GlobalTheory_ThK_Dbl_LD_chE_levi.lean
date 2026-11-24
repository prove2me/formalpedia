-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_chE_levi
-- name    : GlobalTheory.ThK.Dbl.LD.chE_levi
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:03:23.324779+00:00
-- url     : https://prove2.me/theorems/399f634e-3721-474e-8583-5904c8917f1c
-- title:
--   LD: ch E levi
-- statement:
--   The LD construction uses the ch E levi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistC.lean#L62-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistC.lean#L62-L72

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

theorem GlobalTheory.ThK.Dbl.LD.chE_levi (X : Matrix (Fin (n + 1)) (Fin (d + 1)) k) (h : Matrix (Fin d) (Fin d) k) :
    chE (X * blk 1 0 h) = (((chE X).1.1, (chE X).1.2 ᵥ* h), (chE X).2 * h) := by sorry
