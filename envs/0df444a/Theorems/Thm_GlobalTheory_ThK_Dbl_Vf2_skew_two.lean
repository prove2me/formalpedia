-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Vf2_skew_two
-- name    : GlobalTheory.ThK.Dbl.Vf2.skew_two
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T21:03:58.8278+00:00
-- url     : https://prove2.me/theorems/f8c26063-8c27-4630-a5de-fbfd0c9c7b8d
-- title:
--   Vf2: skew two
-- statement:
--   The Vf2 construction uses the skew two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/SkewTwo.lean#L29-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/SkewTwo.lean#L29-L39

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
omit [DecidableEq β]

theorem GlobalTheory.ThK.Dbl.Vf2.skew_two (hc : ∀ z, c (c z) = z) (hG : ∀ i j, c (G j i) = G i j) (u w : β → A) :
    (vecMulVec u (G *ᵥ c ∘ w) - vecMulVec w (G *ᵥ c ∘ u))ᵀ * G +
      G * (vecMulVec u (G *ᵥ c ∘ w) - vecMulVec w (G *ᵥ c ∘ u)).map c = 0 := by sorry
