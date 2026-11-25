-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Bmp_keep
-- name    : GlobalTheory.ThK.Dbl.Bmp.keep
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:41:08.693063+00:00
-- url     : https://prove2.me/theorems/07cc8d2f-d750-4e41-b77f-5b0fca5e0ccf
-- title:
--   Bmp: keep
-- statement:
--   The Bmp construction uses the keep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/MemLam.lean#L68-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/MemLam.lean#L68-L80

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_MemLam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Bmp
open Matrix
variable {O K : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]
variable {a : O} {n d : ℕ}
omit [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O K]

theorem GlobalTheory.ThK.Dbl.Bmp.keep {h : Matrix (Fin n) (Fin n) K} (hh : h - 1 ∈ lam K a n n) (y : Matrix (Fin n) (Fin d) O) {Y : Matrix (Fin n) (Fin d) K}
    (hY : Y - y.map (algebraMap O K) ∈ lam K a n d) : h * Y - y.map (algebraMap O K) ∈ lam K a n d := by sorry
