-- Prove2me | Theorems.Thm_GroundTheory_Brauer_maximal_isMulCommutative_iff_centralizer_eq
-- name    : GroundTheory.Brauer.maximal_isMulCommutative_iff_centralizer_eq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T02:31:55.023803+00:00
-- url     : https://prove2.me/theorems/687ad392-2e10-4877-894a-a425597e9f06
-- title:
--   Brauer: maximal is Mul Commutative iff centralizer eq
-- statement:
--   The Brauer construction uses the maximal is Mul Commutative iff centralizer eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L179-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L179-L196

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

theorem GroundTheory.Brauer.maximal_isMulCommutative_iff_centralizer_eq (F : Subalgebra K D) [IsMulCommutative F] :
    Maximal (fun G : Subalgebra K D ↦ IsMulCommutative G) F ↔
      Subalgebra.centralizer K (F : Set D) = F := by sorry
