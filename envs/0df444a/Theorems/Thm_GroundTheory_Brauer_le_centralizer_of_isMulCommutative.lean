-- Prove2me | Theorems.Thm_GroundTheory_Brauer_le_centralizer_of_isMulCommutative
-- name    : GroundTheory.Brauer.le_centralizer_of_isMulCommutative
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:27:43.994926+00:00
-- url     : https://prove2.me/theorems/71140146-7c2f-58e1-ba06-8a3d69a98050
-- title:
--   Brauer: le centralizer of is Mul Commutative
-- statement:
--   The Brauer construction uses the le centralizer of is Mul Commutative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L161-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L161-L166

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

theorem GroundTheory.Brauer.le_centralizer_of_isMulCommutative (F : Subalgebra K D) [IsMulCommutative F] :
    F ≤ Subalgebra.centralizer K (F : Set D) := by sorry
