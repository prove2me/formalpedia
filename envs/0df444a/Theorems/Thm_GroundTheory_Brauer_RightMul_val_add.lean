-- Prove2me | Theorems.Thm_GroundTheory_Brauer_RightMul_val_add
-- name    : GroundTheory.Brauer.RightMul.val_add
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:27.400513+00:00
-- url     : https://prove2.me/theorems/972bca3a-ea4a-5dc1-83d2-0ecf15f13cc2
-- title:
--   Right Mul: val add
-- statement:
--   The Right Mul construction uses the val add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L90-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L90-L90

import Mathlib
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Degree
import Definitions.Def_GroundTheory_Brauer_Splitting
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

theorem GroundTheory.Brauer.RightMul.val_add (x y : RightMul ι) : (x + y).val = x.val + y.val := by sorry
