-- Prove2me | Theorems.Thm_GroundTheory_Brauer_isSeparable_coe_iff
-- name    : GroundTheory.Brauer.isSeparable_coe_iff
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:28:59.648278+00:00
-- url     : https://prove2.me/theorems/e823cb8d-6d5f-5ddf-8fd5-e48864fdc34d
-- title:
--   Brauer: is Separable coe iff
-- statement:
--   The Brauer construction uses the is Separable coe iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L50-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L50-L54

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

theorem GroundTheory.Brauer.isSeparable_coe_iff {A : Type*} [Ring A] [Algebra K A] {S : Subalgebra K A} (x : S) :
    IsSeparable K (x : A) ↔ IsSeparable K x := by sorry
