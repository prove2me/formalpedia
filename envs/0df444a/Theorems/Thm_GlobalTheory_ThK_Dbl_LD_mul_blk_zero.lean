-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_mul_blk_zero
-- name    : GlobalTheory.ThK.Dbl.LD.mul_blk_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:53.933356+00:00
-- url     : https://prove2.me/theorems/d4b63a0c-b4f0-4d44-9db5-a72095140449
-- title:
--   LD: mul blk zero
-- statement:
--   The LD construction uses the mul blk zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistC.lean#L19-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistC.lean#L19-L20

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

theorem GlobalTheory.ThK.Dbl.LD.mul_blk_zero {m : Type} (X : Matrix m (Fin (d + 1)) k) (a : k) (b : Fin d → k) (h : Matrix (Fin d) (Fin d) k) (i : m) :
    (X * blk a b h) i 0 = X i 0 * a := by sorry
