-- Prove2me | Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_val_smul
-- name    : GroundTheory.Brauer.SkolemNoether.Twist.val_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:45:41.687648+00:00
-- url     : https://prove2.me/theorems/bb937a93-20bf-4bd4-8dc3-b20a4909e1b7
-- title:
--   Twist: val smul
-- statement:
--   The Twist construction uses the val smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/SkolemNoether.lean#L83-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/SkolemNoether.lean#L83-L83

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

theorem GroundTheory.Brauer.SkolemNoether.Twist.val_smul (r : A ⊗[K] Bᵐᵒᵖ) (x : Twist f) : (r • x).val = bimoduleHom f r x.val := by sorry
