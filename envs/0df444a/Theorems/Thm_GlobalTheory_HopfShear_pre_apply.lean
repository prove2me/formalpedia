-- Prove2me | Theorems.Thm_GlobalTheory_HopfShear_pre_apply
-- name    : GlobalTheory.HopfShear.pre_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:37:40.523159+00:00
-- url     : https://prove2.me/theorems/3ec7a75a-20bd-4e7a-85e6-da6bbcd838e5
-- title:
--   Hopf Shear: pre apply
-- statement:
--   The Hopf Shear construction uses the pre apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PointsGroup.lean#L40-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PointsGroup.lean#L40-L41

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

theorem GlobalTheory.HopfShear.pre_apply (f : B →ₐc[R] A) (x : WithConv (A →ₐ[R] X)) (b : B) :
    (pre f x).ofConv b = x.ofConv (f b) := by sorry
