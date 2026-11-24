-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Vf2_rank_lt
-- name    : GlobalTheory.ThK.Dbl.Vf2.rank_lt
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:03:49.884377+00:00
-- url     : https://prove2.me/theorems/6b55570e-14f1-4f08-b23f-bc6a9fcd8dd6
-- title:
--   Vf2: rank lt
-- statement:
--   The Vf2 construction uses the rank lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/SkewTwo.lean#L15-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/SkewTwo.lean#L15-L24

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LocalTheory_ConeShifts_ExistsPowIdem
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_SkewTwo
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Vf2
open Matrix GlobalTheory.WeilM PositivityTheory.ThKG.Loc.Cone.Vf
variable {A K β : Type} [CommRing A] [Field K] [Fintype β] [DecidableEq β]
omit [DecidableEq β]

theorem GlobalTheory.ThK.Dbl.Vf2.rank_lt {M : Matrix β β K} {y w φ : β → K} (hy : M *ᵥ y = 0) (hw : w ∉ LinearMap.range M.mulVecLin) (hφ : φ ⬝ᵥ y ≠ 0) :
    M.rank < (M + vecMulVec w φ).rank := by sorry
