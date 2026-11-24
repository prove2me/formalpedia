-- Prove2me | Theorems.Thm_GlobalTheory_whiskerLeft_left_isPullback_snd
-- name    : GlobalTheory.whiskerLeft_left_isPullback_snd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:24:25.811799+00:00
-- url     : https://prove2.me/theorems/95d892f4-1d0b-4bae-9369-86a8b62126b0
-- title:
--   Global Theory: whisker Left left is Pullback snd
-- statement:
--   The Global Theory construction uses the whisker Left left is Pullback snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WhiskerLeftLeftIsPullbackSnd.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WhiskerLeftLeftIsPullbackSnd.lean#L7-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WhiskerLeftLeftIsPullbackSnd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory

theorem GlobalTheory.whiskerLeft_left_isPullback_snd (S : Scheme.{0}) (U T T' : Over S) (f : T' ⟶ T) :
    IsPullback (U ◁ f).left (snd U T').left (snd U T).left f.left := by sorry
