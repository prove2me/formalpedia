-- Prove2me | Theorems.Thm_GroundTheory_Automorphic_Whittaker_colsTo_mul_self
-- name    : GroundTheory.Automorphic.Whittaker.colsTo_mul_self
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:41:11.509259+00:00
-- url     : https://prove2.me/theorems/57029d14-83ca-4724-baf5-cbfab40b97af
-- title:
--   Whittaker: cols To mul self
-- statement:
--   The Whittaker construction uses the cols To mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L96-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/AutomorphicForms/WhittakerCells.lean#L96-L101

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_FiniteBruhat
import Definitions.Def_GroundTheory_AutomorphicForms_Iwasawa
import Definitions.Def_GroundTheory_AutomorphicForms_WhittakerCells
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic
open GroundTheory.Automorphic.Whittaker
open Matrix DoubleCoset
variable {F : Type*} [Field F] {n : ℕ}

theorem GroundTheory.Automorphic.Whittaker.colsTo_mul_self (j : Fin n) :
    colsTo j * colsTo j = (colsTo j : Matrix (Fin n) (Fin n) F) := by sorry
