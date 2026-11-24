-- Prove2me | Theorems.Thm_GlobalTheory_T_isPullback_whiskerLeft_left_snd
-- name    : GlobalTheory.T.isPullback_whiskerLeft_left_snd
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:49:14.033546+00:00
-- url     : https://prove2.me/theorems/b3819eaa-ebfc-4cce-8e11-0918710b046f
-- title:
--   T: is Pullback whisker Left left snd
-- statement:
--   The T construction uses the is Pullback whisker Left left snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WhiskerLeftLeftIsPullbackSndStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/WhiskerLeftLeftIsPullbackSndStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WhiskerLeftLeftIsPullbackSnd
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_WhiskerLeftLeftIsPullbackSndStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isPullback_whiskerLeft_left_snd : ∀ (S : Scheme.{0}) (U T T' : Over S) (f : T' ⟶ T), IsPullback (U ◁ f).left (snd U T').left (snd U T).left f.left := by sorry
