-- Prove2me | Theorems.Thm_GroundTheory_Brauer_isMulCommutative_adjoin_insert
-- name    : GroundTheory.Brauer.isMulCommutative_adjoin_insert
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T02:29:27.273921+00:00
-- url     : https://prove2.me/theorems/2b6b493c-ca4a-5a03-8f32-98cfb19249b8
-- title:
--   Brauer: is Mul Commutative adjoin insert
-- statement:
--   The Brauer construction uses the is Mul Commutative adjoin insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L168-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L168-L177

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
variable {K : Type*} [Field K] {D : Type*} [DivisionRing D] [Algebra K D]

theorem GroundTheory.Brauer.isMulCommutative_adjoin_insert (F : Subalgebra K D) [IsMulCommutative F] {y : D}
    (hy : y ∈ Subalgebra.centralizer K (F : Set D)) :
    IsMulCommutative (Algebra.adjoin K (insert y (F : Set D))) := by sorry
