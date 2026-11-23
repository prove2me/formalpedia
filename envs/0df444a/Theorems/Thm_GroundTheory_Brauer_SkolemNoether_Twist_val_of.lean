-- Prove2me | Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_val_of
-- name    : GroundTheory.Brauer.SkolemNoether.Twist.val_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:06:58.000237+00:00
-- url     : https://prove2.me/theorems/f4b87dc3-9584-4cd3-8255-231f4691c8a4
-- title:
--   Twist: val of
-- statement:
--   The Twist construction uses the val of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/SkolemNoether.lean#L90-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/SkolemNoether.lean#L90-L90

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

theorem GroundTheory.Brauer.SkolemNoether.Twist.val_of (x : A) : (of f x).val = x := by sorry

attribute [defeq] GroundTheory.Brauer.SkolemNoether.Twist.val_of
