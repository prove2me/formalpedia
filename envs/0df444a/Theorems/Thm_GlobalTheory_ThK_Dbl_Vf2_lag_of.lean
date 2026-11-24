-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Vf2_lag_of
-- name    : GlobalTheory.ThK.Dbl.Vf2.lag_of
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:04:14.194912+00:00
-- url     : https://prove2.me/theorems/9a619fa4-a584-4c99-8ced-5fee0f7bd24f
-- title:
--   Vf2: lag of
-- statement:
--   The Vf2 construction uses the lag of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/SkewTwo.lean#L148-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/SkewTwo.lean#L148-L163

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
variable {R A β : Type} [CommRing R] [CommRing A] [Algebra R A] {c : A →ₐ[R] A} [Fintype β] [DecidableEq β] {J : Matrix β β A}

theorem GlobalTheory.ThK.Dbl.Vf2.lag_of {b b' x y : Matrix β β A} (b1 : Adj c J b b') (hb : b + b' = -1) (g : UG c (dbl J))
    (hg : g.1.1 * (diagCols β : Matrix (β ⊕ β) β A) = fromRows x y) :
    (y + b * (y - x))ᵀ * J * (y - x).map c + (y - x)ᵀ * J * (y + b * (y - x)).map c = 0 := by sorry
