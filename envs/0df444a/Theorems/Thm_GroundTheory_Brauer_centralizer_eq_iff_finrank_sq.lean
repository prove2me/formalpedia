-- Prove2me | Theorems.Thm_GroundTheory_Brauer_centralizer_eq_iff_finrank_sq
-- name    : GroundTheory.Brauer.centralizer_eq_iff_finrank_sq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:15:30.151432+00:00
-- url     : https://prove2.me/theorems/c9a49bea-612c-4312-8471-196e6d6132a6
-- title:
--   Brauer: centralizer eq iff finrank sq
-- statement:
--   The Brauer construction uses the centralizer eq iff finrank sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L200-L215
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L200-L215

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
variable [Algebra.IsCentral K D] [FiniteDimensional K D]

theorem GroundTheory.Brauer.centralizer_eq_iff_finrank_sq (F : Subalgebra K D) [IsMulCommutative F] :
    Subalgebra.centralizer K (F : Set D) = F ↔ finrank K F ^ 2 = finrank K D := by sorry
