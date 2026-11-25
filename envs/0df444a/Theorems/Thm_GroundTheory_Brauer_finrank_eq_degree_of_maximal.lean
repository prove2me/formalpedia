-- Prove2me | Theorems.Thm_GroundTheory_Brauer_finrank_eq_degree_of_maximal
-- name    : GroundTheory.Brauer.finrank_eq_degree_of_maximal
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T03:16:02.148933+00:00
-- url     : https://prove2.me/theorems/d65120b1-4c34-47de-a536-831bc04696ef
-- title:
--   Brauer: finrank eq degree of maximal
-- statement:
--   The Brauer construction uses the finrank eq degree of maximal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L228-L231
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L228-L231

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

theorem GroundTheory.Brauer.finrank_eq_degree_of_maximal (F : Subalgebra K D) [IsMulCommutative F]
    (hF : Maximal (fun G : Subalgebra K D ↦ IsMulCommutative G) F) :
    finrank K F = degree K D := by sorry
