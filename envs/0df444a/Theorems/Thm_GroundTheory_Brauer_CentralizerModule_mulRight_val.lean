-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CentralizerModule_mulRight_val
-- name    : GroundTheory.Brauer.CentralizerModule.mulRight_val
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:54.422858+00:00
-- url     : https://prove2.me/theorems/12a8a92d-2504-4b98-b921-c45a6a4d1c86
-- title:
--   Centralizer Module: mul Right val
-- statement:
--   The Centralizer Module construction uses the mul Right val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/DoubleCentralizer.lean#L114-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/DoubleCentralizer.lean#L114-L115

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
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
open SkolemNoether
variable {K A : Type*} [Field K] [Ring A] [Algebra K A] (B : Subalgebra K A)
open GroundTheory.Brauer.CentralizerModule

theorem GroundTheory.Brauer.CentralizerModule.mulRight_val (c : Subalgebra.centralizer K (B : Set A)) (x : Twist B.val) :
    (mulRight B c x).val = x.val * c := by sorry
