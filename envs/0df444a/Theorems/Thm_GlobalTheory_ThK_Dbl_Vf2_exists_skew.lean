-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Vf2_exists_skew
-- name    : GlobalTheory.ThK.Dbl.Vf2.exists_skew
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:41:09.250119+00:00
-- url     : https://prove2.me/theorems/227a19aa-9091-53b8-9c9b-637b7406adab
-- title:
--   Vf2: exists skew
-- statement:
--   The Vf2 construction uses the exists skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/SkewTwo.lean#L100-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/SkewTwo.lean#L100-L142

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

theorem GlobalTheory.ThK.Dbl.Vf2.exists_skew (hc : ∀ z, c (c z) = z) (hr : Function.Surjective r) (hG : ∀ i j, c (G j i) = G i j) (hG' : G * G' = 1)
    (hcase : ((∀ z, r z = 0 → r (c z) = 0) ∧ ∃ κ, r (κ - c κ) ≠ 0) ∨ ∃ η, r η = 1 ∧ r (c η) = 0)
    (hu : ∀ z, r z ≠ 0 → r (c z) ≠ 0 → IsUnit z)
    (lag : Mᵀ * G * m.map c + mᵀ * G * M.map c = 0) (inj : P * M + Q * m = 1) :
    ∃ S : Matrix β β A, Sᵀ * G + G * S.map c = 0 ∧ IsUnit (M + S * m).det := by sorry
