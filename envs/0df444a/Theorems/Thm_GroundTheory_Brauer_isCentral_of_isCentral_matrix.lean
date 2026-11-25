-- Prove2me | Theorems.Thm_GroundTheory_Brauer_isCentral_of_isCentral_matrix
-- name    : GroundTheory.Brauer.isCentral_of_isCentral_matrix
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:55.492385+00:00
-- url     : https://prove2.me/theorems/3b2b2d8e-55f0-4a00-94a3-78c051fbf6db
-- title:
--   Brauer: is Central of is Central matrix
-- statement:
--   The Brauer construction uses the is Central of is Central matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/IsBrauerEquivalentIffNonemptyAlgEquiv.lean#L307-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/IsBrauerEquivalentIffNonemptyAlgEquiv.lean#L307-L319

import Mathlib
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
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
open TensorProduct
universe u v w
variable {K : Type u} [Field K]

theorem GroundTheory.Brauer.isCentral_of_isCentral_matrix {D : Type w} [Ring D] [Algebra K D] {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι] [Algebra.IsCentral K (Matrix ι ι D)] :
    Algebra.IsCentral K D := by sorry
