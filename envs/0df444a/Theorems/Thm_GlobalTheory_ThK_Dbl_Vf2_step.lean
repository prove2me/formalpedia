-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Vf2_step
-- name    : GlobalTheory.ThK.Dbl.Vf2.step
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:04:01.162359+00:00
-- url     : https://prove2.me/theorems/8583ead3-a8c2-48a4-a8a8-2aa03963dd09
-- title:
--   Vf2: step
-- statement:
--   The Vf2 construction uses the step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/SkewTwo.lean#L41-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/SkewTwo.lean#L41-L98

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
variable {c : A →+* A} {r : A →+* K} {G G' M m P Q : Matrix β β A}

theorem GlobalTheory.ThK.Dbl.Vf2.step (hc : ∀ z, c (c z) = z) (hr : Function.Surjective r) (hG : ∀ i j, c (G j i) = G i j) (hG' : G * G' = 1)
    (hcase : ((∀ z, r z = 0 → r (c z) = 0) ∧ ∃ κ, r (κ - c κ) ≠ 0) ∨ ∃ η, r η = 1 ∧ r (c η) = 0)
    (lag : Mᵀ * G * m.map c + mᵀ * G * M.map c = 0) (inj : P * M + Q * m = 1) (h0 : (M.map r).det = 0) :
    ∃ S : Matrix β β A, Sᵀ * G + G * S.map c = 0 ∧ (M.map r).rank < ((M + S * m).map r).rank := by sorry
