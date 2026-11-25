-- Prove2me | Theorems.Thm_GroundTheory_Brauer_finrank_baseChange_eq
-- name    : GroundTheory.Brauer.finrank_baseChange_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:20:12.60081+00:00
-- url     : https://prove2.me/theorems/01842469-92c6-4270-a75c-f45c0b9aa7a0
-- title:
--   Brauer: finrank base Change eq
-- statement:
--   The Brauer construction uses the finrank base Change eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/BaseChangeCSA.lean#L30-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/BaseChangeCSA.lean#L30-L31

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
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
open TensorProduct Algebra.TensorProduct
variable (K L A : Type*) [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]

theorem GroundTheory.Brauer.finrank_baseChange_eq : Module.finrank L (L ⊗[K] A) = Module.finrank K A := by sorry
