-- Prove2me | Theorems.Thm_GroundTheory_Brauer_RightMul_val_smul
-- name    : GroundTheory.Brauer.RightMul.val_smul
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:56:09.254673+00:00
-- url     : https://prove2.me/theorems/d01d16e7-f9c8-4e07-a7c8-c740c6d488dc
-- title:
--   Right Mul: val smul
-- statement:
--   The Right Mul construction uses the val smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L88-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L88-L88

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Degree
import Definitions.Def_GroundTheory_Brauer_Splitting
import Theorems.Thm_GroundTheory_Brauer_SkolemNoether_Twist_val_smul

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
open TensorProduct Module
universe u v w
variable {K : Type*} [Field K] {A : Type*} [Ring A] [Algebra K A] {L : Type*} [Field L]
  [Algebra K L]
open GroundTheory.Brauer.RightMul
variable (ι : L →ₐ[K] A)

theorem GroundTheory.Brauer.RightMul.val_smul (l : L) (x : RightMul ι) : (l • x).val = x.val * ι l := by sorry
