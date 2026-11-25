-- Prove2me | Theorems.Thm_GlobalTheory_HopfShear_post_apply
-- name    : GlobalTheory.HopfShear.post_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:07:24.242049+00:00
-- url     : https://prove2.me/theorems/d85fa0b6-a97c-47b1-9e98-e4b1d1d68b4e
-- title:
--   Hopf Shear: post apply
-- statement:
--   The Hopf Shear construction uses the post apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PointsGroup.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PointsGroup.lean#L43-L44

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PointsGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct WithConv
open GlobalTheory GlobalTheory.HopfShear
variable {R A B X Y : Type} [CommRing R] [CommRing A] [CommRing B] [CommRing X] [CommRing Y]
  [HopfAlgebra R A] [HopfAlgebra R B] [Algebra R X] [Algebra R Y]
attribute [local instance] pointsGroup

theorem GlobalTheory.HopfShear.post_apply (h : X →ₐ[R] Y) (x : WithConv (A →ₐ[R] X)) (a : A) :
    (post h x).ofConv a = h (x.ofConv a) := by sorry
