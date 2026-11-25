-- Prove2me | Theorems.Thm_GroundTheory_Brauer_exists_maximal_isSeparable
-- name    : GroundTheory.Brauer.exists_maximal_isSeparable
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T03:14:39.825895+00:00
-- url     : https://prove2.me/theorems/69e177ab-2ce8-44a0-813b-b5a51801c53b
-- title:
--   Brauer: exists maximal is Separable
-- statement:
--   The Brauer construction uses the exists maximal is Separable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L242-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L242-L329

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

theorem GroundTheory.Brauer.exists_maximal_isSeparable :
    ∃ F : Subalgebra K D, IsMulCommutative F ∧
      Maximal (fun G : Subalgebra K D ↦ IsMulCommutative G) F ∧ ∀ x ∈ F, IsSeparable K x := by sorry
