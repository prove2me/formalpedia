-- Prove2me | Theorems.Thm_GroundTheory_Brauer_BrauerGroup_baseChange_comp
-- name    : GroundTheory.Brauer.BrauerGroup.baseChange_comp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:11:41.847979+00:00
-- url     : https://prove2.me/theorems/8be5a8aa-e2bd-40fa-ab84-a3cec2e4daa1
-- title:
--   Brauer Group: base Change comp
-- statement:
--   The Brauer Group construction uses the base Change comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/BaseChange.lean#L48-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/BaseChange.lean#L48-L53

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

theorem GroundTheory.Brauer.BrauerGroup.baseChange_comp (M : Type u) [Field M] [Algebra K M] [Algebra L M]
    [IsScalarTower K L M] :
    (baseChange L M).comp (baseChange K L) = baseChange K M := by sorry
