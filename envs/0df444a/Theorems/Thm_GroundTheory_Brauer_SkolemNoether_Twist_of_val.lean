-- Prove2me | Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_of_val
-- name    : GroundTheory.Brauer.SkolemNoether.Twist.of_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:54.579244+00:00
-- url     : https://prove2.me/theorems/e6466fde-e767-4d81-8614-5ffb3cac9650
-- title:
--   Twist: of val
-- statement:
--   The Twist construction uses the of val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/SkolemNoether.lean#L92-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/SkolemNoether.lean#L92-L92

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Brauer
open TensorProduct
open GroundTheory.Brauer.SkolemNoether
variable {K A B : Type*} [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
open GroundTheory.Brauer.SkolemNoether.Twist
variable (f : B →ₐ[K] A)

theorem GroundTheory.Brauer.SkolemNoether.Twist.of_val (x : Twist f) : of f x.val = x := by sorry

attribute [defeq] GroundTheory.Brauer.SkolemNoether.Twist.of_val
