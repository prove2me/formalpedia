-- Prove2me | Theorems.Thm_GroundTheory_Brauer_baseChangeTensor_tmul
-- name    : GroundTheory.Brauer.baseChangeTensor_tmul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:23:23.993675+00:00
-- url     : https://prove2.me/theorems/da84f2f5-2b7d-485f-8083-067308353ab8
-- title:
--   Brauer: base Change Tensor tmul
-- statement:
--   The Brauer construction uses the base Change Tensor tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/BaseChangeCSA.lean#L114-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/BaseChangeCSA.lean#L114-L115

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
variable (K L A B : Type*) [CommSemiring K] [CommSemiring L] [Algebra K L] [Semiring A]
  [Algebra K A] [Semiring B] [Algebra K B]

theorem GroundTheory.Brauer.baseChangeTensor_tmul (l : L) (a : A) (b : B) :
    baseChangeTensor K L A B (l ⊗ₜ (a ⊗ₜ b)) = (l ⊗ₜ a) ⊗ₜ (1 ⊗ₜ b) := by sorry

attribute [defeq] GroundTheory.Brauer.baseChangeTensor_tmul
