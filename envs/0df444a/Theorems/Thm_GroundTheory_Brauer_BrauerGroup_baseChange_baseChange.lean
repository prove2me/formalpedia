-- Prove2me | Theorems.Thm_GroundTheory_Brauer_BrauerGroup_baseChange_baseChange
-- name    : GroundTheory.Brauer.BrauerGroup.baseChange_baseChange
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T01:11:57.798176+00:00
-- url     : https://prove2.me/theorems/d379e56c-88ba-4a08-a697-b028892b1efa
-- title:
--   Brauer Group: base Change base Change
-- statement:
--   The Brauer Group construction uses the base Change base Change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/BaseChange.lean#L55-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/BaseChange.lean#L55-L58

import Mathlib
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_BaseChange
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
universe u v
open GroundTheory.Brauer.BrauerGroup
variable (K : Type u) [Field K] (L : Type u) [Field L] [Algebra K L]

theorem GroundTheory.Brauer.BrauerGroup.baseChange_baseChange (M : Type u) [Field M] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] (x : BrauerGroup.{u, u} K) :
    baseChange L M (baseChange K L x) = baseChange K M x := by sorry
