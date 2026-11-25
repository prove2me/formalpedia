-- Prove2me | Theorems.Thm_GroundTheory_Brauer_isSimpleRing_of_finiteDimensional
-- name    : GroundTheory.Brauer.isSimpleRing_of_finiteDimensional
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T02:29:26.522807+00:00
-- url     : https://prove2.me/theorems/a9ee12c0-a12c-5de4-a86c-3dc4ea64df43
-- title:
--   Brauer: is Simple Ring of finite Dimensional
-- statement:
--   The Brauer construction uses the is Simple Ring of finite Dimensional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L45-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Splitting.lean#L45-L48

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

theorem GroundTheory.Brauer.isSimpleRing_of_finiteDimensional (S : Subalgebra K D) [FiniteDimensional K S] :
    IsSimpleRing S := by sorry
