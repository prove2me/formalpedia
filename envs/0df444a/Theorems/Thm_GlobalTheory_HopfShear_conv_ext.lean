-- Prove2me | Theorems.Thm_GlobalTheory_HopfShear_conv_ext
-- name    : GlobalTheory.HopfShear.conv_ext
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T14:37:39.086792+00:00
-- url     : https://prove2.me/theorems/54b212eb-5339-47cd-bd4c-22c11d1cb3b8
-- title:
--   Hopf Shear: conv ext
-- statement:
--   The Hopf Shear construction uses the conv ext property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PointsGroup.lean#L46-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PointsGroup.lean#L46-L47

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

theorem GlobalTheory.HopfShear.conv_ext {x y : WithConv (A →ₐ[R] X)} (h : ∀ a, x.ofConv a = y.ofConv a) : x = y := by sorry
